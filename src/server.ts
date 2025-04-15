import * as vscode from 'vscode';
import * as child_process from 'child_process';
import * as path from 'path';
import { TextEncoder } from 'util';
import {
    Annotation, DefinitionInfo, HoverInfo, Location, Markup, Message, Position, Pretty,
    PrettyElem, PrettyString, Section, SectionHeader, Style
} from './serverTypes';
import { log } from './common';

type Receiver = {
    resolve: (value: string | PromiseLike<string>) => void,
    reject: (reason?: any) => void
}

/** Similar to `HolKernel`, but used for backend tasks. Instead of a user-level terminal interface,
 * it presents an asynchronous interface for passing data to and from ML.
 */
export class HolServer {
    /**
     * The connection to the HOL process itself. May be undefined if the process has not started yet
     * or if it was aborted etc.
     */
    private child?: child_process.ChildProcess;

    public lastVersion: number = NaN;
    public lineCounts: LineCounter = new LineCounter('');
    public messageListener: (msgs: Message[]) => void = () => { };
    private receiver: Receiver | undefined;
    private stdoutBuffer: string[] = [];
    private stderrBuffer: string[] = [];
    private isErr: boolean = false;
    private initFailed: boolean = false;

    constructor(private cwd: string, private holPath: string) { }

    get running(): boolean { return !!this.child; }

    sendRaw(text: string) {
        if (this.child) {
            // log(`send ${JSON.stringify(text)}\n${text}`);
            this.child?.stdin?.write(text);
        }
    }

    start(prelude: () => Promise<void>): Promise<void> {
        this.child = child_process.spawn(path.join(this.holPath, 'bin', 'hol'), ['--zero'], {
            // eslint-disable-next-line @typescript-eslint/naming-convention
            env: { ...process.env, ...{ HOLIDE_ASYNC_FD: '3' } },
            stdio: ['pipe', 'pipe', 'pipe', 'pipe'], // open another pipe for async stuff
            cwd: this.cwd,
            detached: true,
        });
        // log(`starting server ${this.child.pid}`);
        const asyncBuffer: string[] = [];
        function parse(s: string): any {
            try {
                return JSON.parse(s)
            } catch (e) { console.error(s, e); }
        }
        this.child.stdio[3]?.addListener('data', (data: Buffer) => {
            if (!data.length) return;
            // log(`recv async:\n${JSON.stringify(data.toString())}`);
            let i = data.indexOf(0);
            if (i >= 0) {
                asyncBuffer.push(data.toString(undefined, undefined, i));
                const msgs = [parse(asyncBuffer.join(''))];
                while (true) {
                    const j = data.indexOf(0, i + 1);
                    if (j < 0) break;
                    msgs.push(parse(data.toString(undefined, i + 1, j)));
                    i = j;
                }
                try {
                    this.messageListener(msgs);
                } catch (e) { console.error(msgs, e); }
                asyncBuffer.length = 0;
                if (i + 1 < data.length) asyncBuffer.push(data.toString(undefined, i + 1));
            } else {
                asyncBuffer.push(data.toString());
            }
        });
        const pid = this.child.pid;
        const onKilled = () => { if (pid === this.child?.pid) this.onKilled() };
        this.child?.addListener('disconnect', onKilled);
        this.child?.addListener('close', onKilled);
        this.child?.addListener('exit', onKilled);
        this.child?.stdout?.on('data', (data: Buffer) => {
            if (!data.length) return;
            // log(`recv stdout:\n${JSON.stringify(data.toString())}`);
            if (data.readUint8(data.length - 1) === 0) {
                if (this.stderrBuffer.length) {
                    console.warn('stderr: ' + this.stderrBuffer.join('').replace(/\n/g, '\nstderr: '));
                    this.stderrBuffer.length = 0;
                }
                this.stdoutBuffer.push(data.toString(undefined, undefined, data.length - 1));
                if (!this.receiver) {
                    // log(`got message but no one is listening:\n${JSON.stringify(this.stdoutBuffer.join(''))}`);
                } else if (this.isErr) {
                    this.receiver.reject();
                } else {
                    this.receiver.resolve(this.stdoutBuffer.join(''));
                }
                this.resetRecv();
            } else {
                this.stdoutBuffer.push(data.toString());
            }
        });
        this.child?.stderr?.on('data', (data: Buffer) => {
            if (!data.length) return;
            // log(`recv stderr:\n${JSON.stringify(data.toString())}`);
            const s = data.toString();
            if (s.includes('error:')) this.isErr = true;
            const nl = s.lastIndexOf('\n');
            if (nl >= 0) {
                if (nl > 0) this.stderrBuffer.push(s.substring(0, nl));
                if (this.stderrBuffer.length) {
                    console.warn(Date.now(), 'stderr: ' + this.stderrBuffer.join('').replace(/\n/g, '\nstderr: '));
                    this.stderrBuffer.length = 0;
                }
                if (nl + 1 < s.length) this.stderrBuffer.push(s.substring(nl + 1));
            } else {
                this.stderrBuffer.push(s);
            }
        });

        return this.receive().then(prelude).catch(reason => {
            this.initFailed = true;
            throw reason;
        });
    }

    resetRecv() {
        this.isErr = false;
        this.stdoutBuffer.length = 0;
        if (this.stderrBuffer.length) {
            console.warn('stderr: ' + this.stderrBuffer.join('').replace(/\n/g, '\nstderr: '));
            this.stderrBuffer.length = 0;
        }
        this.receiver = undefined;
        if (this.initFailed) throw 'initialization failed';
    }

    receive(): Promise<string> {
        return new Promise((resolve, reject) => this.receiver = { resolve, reject });
    }


    send(...s: string[]) {
        // log(`send:\n${JSON.stringify(s.join(''))}`);
        s.push('\0'); this.sendRaw(s.join(''));

    }

    request(...s: string[]): Promise<string> {
        this.resetRecv();
        this.send(...s);
        return this.receive();
    }

    async requestJSON<T>(...s: string[]): Promise<T> {
        return JSON.parse(await this.request(...s));
    }

    stop() {
        if (this.child?.pid) {
            // log(`killing server ${this.child.pid}`);
            process.kill(this.child.pid, 'SIGTERM');
        }
        this.onKilled();
    }

    private onKilled() {
        console.error(`server ${this.child?.pid} killed`);
        this.child = undefined;
        this.receiver?.reject();
        this.receiver = undefined;
    }

    interrupt() {
        if (this.child?.pid) {
            // log(`interrupting server ${this.child.pid}`);
            process.kill(this.child.pid, 'SIGINT');
        }
    }

    sync() {
        if (this.child && (this.child.killed || !this.child.pid || this.child?.exitCode != null)) {
            // log(`mystery death of server`);
            this.onKilled();
        }
    }

    async ensureRunning(prelude: () => Promise<void>) {
        this.sync();
        if (!this.running) await this.start(prelude);
    }

    async setFileContents(text: string, version: number): Promise<void> {
        this.lastVersion = version;
        this.lineCounts = new LineCounter(text);
        const result = await this.request(`val _ = VSCode.setFileContents ${escapeMLString(text)}`);
        if (result) log(`setFileContents was noisy:\n${result}`);
    }

    getHoverInfo([[sline, scol], [eline, ecol]]: Location): Promise<HoverInfo[]> {
        return this.requestJSON(
            `val _ = VSCode.getHoverInfo (${sline}, ${scol}) (${eline}, ${ecol})`);
    }

    gotoDefinition([line, col]: Position): Promise<DefinitionInfo[]> {
        return this.requestJSON(`val _ = VSCode.gotoDefinition (${line}, ${col})`);
    }

    utf8ToPosition(pos: Position): vscode.Position {
        return this.lineCounts.utf8ToPosition(pos);
    }

    utf8ToRange([start, end]: Location): vscode.Range {
        return new vscode.Range(this.utf8ToPosition(start), this.utf8ToPosition(end));
    }

    positionToUtf8(pos: vscode.Position): Position {
        return this.lineCounts.positionToUtf8(pos);
    }

    rangeToUtf8(range: vscode.Range): Location {
        return [this.positionToUtf8(range.start), this.positionToUtf8(range.end)];
    }

    dispose() { this.stop() }
}

/** Encode a string as a UTF-8 encoded ML string literal. */
export const escapeMLString = (() => {
    const nextEscape = /[^!-~ ]|[\\"]/g;
    const encoder = new TextEncoder();
    const encoded = new Uint8Array(4);
    return (str: string) => {
        const buffer = ['"'];
        let match;
        let index = 0;
        while ((match = nextEscape.exec(str))) {
            if (index < match.index) buffer.push(str.substring(index, match.index));
            index = nextEscape.lastIndex;
            const code = str.codePointAt(match.index)!;
            switch (code) {
                case 7: buffer.push('\\a'); break;
                case 8: buffer.push('\\b'); break;
                case 9: buffer.push('\\t'); break;
                case 10: buffer.push('\\n'); break;
                case 11: buffer.push('\\v'); break;
                case 12: buffer.push('\\f'); break;
                case 13: buffer.push('\\r'); break;
                case 34: buffer.push('\\"'); break;
                case 92: buffer.push('\\\\'); break;
                default: {
                    if (code < 32) {
                        buffer.push('\\^', String.fromCharCode(code + 64));
                    } else {
                        const size = encoder.encodeInto(str.charAt(match.index), encoded).written;
                        for (const n of encoded.subarray(0, size)) {
                            buffer.push(`\\${n}`); // note: n >= 128 so this is always 3 chars
                        }
                    }
                }
            }
        }
        if (index < str.length) buffer.push(str.substring(index));
        buffer.push('"');
        return buffer.join('');
    }
})();

class LineCounter {
    private lines: number[] = [];
    constructor(private text: string) {
        let index = 0;
        let next;
        while ((next = text.indexOf('\n', index)) >= 0) {
            index = next + 1;
            this.lines.push(index);
        }
    }

    utf8ToPosition([line, col]: Position): vscode.Position {
        const lineStart = this.lines[line - 1] ?? 0;
        let target = lineStart + col;
        for (let i = lineStart; i < target; i++) {
            const n = this.text.charCodeAt(i);
            if (n < 0x80) { }
            else if (n < 0x800) target--;
            else if (n < 0x10000) target -= 2;
            else { target -= 2; i++; }
        }
        return new vscode.Position(line, target - lineStart);
    }

    positionToUtf8(pos: vscode.Position): Position {
        const lineStart = this.lines[pos.line - 1] ?? 0;
        let col = pos.character;
        for (let i = lineStart; i < lineStart + pos.character; i++) {
            const n = this.text.charCodeAt(i);
            if (n < 0x80) { }
            else if (n < 0x800) col++;
            else if (n < 0x10000) col += 2;
            else { col += 2; i++; }
        }
        return [pos.line, col]
    }
}

export function manpageToMarkdown(manpage: Section[]): vscode.MarkdownString {
    const out = new vscode.MarkdownString;
    function toInlineCode(code: string) {
        const n = code.match(/^`+/gm)?.reduce((a, b) => (a.length > b.length ? a : b)).length ?? 0;
        const fence = '`'.repeat(n + 1);
        return fence + code + fence;
    }
    const escapeText = (text: string) =>
        text.replace(/[\\`*_{}[\]()#+\-!~]/g, '\\$&').replace(/\>/gm, '\\>');

    const getSec = (header: SectionHeader) => {
        const sec = manpage
            .find(sec => sec.kind == 'field' && sec.header == header)
            ?.value as Markup[] | undefined;
        return sec?.length == 1 && typeof sec[0] === 'string' ? sec[0] : undefined;
    }
    for (const section of manpage) {
        switch (section.kind) {
            case 'type':
                let structure = getSec('STRUCTURE') || getSec('LIBRARY');
                const value = structure
                    ? structure.trim() + '.' + section.value
                    : section.value;
                out.appendCodeblock(value, 'hol4');
                out.appendMarkdown('\n---');
                break;
            case 'field':
                switch (section.header) {
                    case 'DOC': case 'STRUCTURE': case 'LIBRARY': case 'KEYWORDS': continue;
                    case 'SYNOPSIS': case 'DESCRIBE': break;
                    case 'COMMENTS': out.appendMarkdown(`### Comments\n\n`); break;
                    case 'USES': out.appendMarkdown(`### Uses\n\n`); break;
                    case 'FAILURE': out.appendMarkdown(`### Failure\n\n`); break;
                    case 'EXAMPLE': out.appendMarkdown(`### Example\n\n`); break;
                }
                for (const markup of section.value) {
                    if (typeof markup === 'string') out.appendMarkdown(escapeText(markup));
                    else if (Array.isArray(markup)) out.appendMarkdown('\n\n');
                    else if ('code' in markup) out.appendMarkdown(toInlineCode(markup.code));
                    else if ('xmpl' in markup) out.appendCodeblock(markup.xmpl.trim(), 'hol4');
                    else out.appendMarkdown('*' + escapeText(markup.emph) + '*');
                }
                break;
            case 'seeAlso':
                const code = section.value.map(s => toInlineCode(s.trim()));
                out.appendMarkdown(`### See Also\n${code.join(', ')}`);
                break;
        }
        out.appendMarkdown('\n\n');
    }
    out.appendMarkdown('\n---\n')
    return out;
}

function parsePretty(value: PrettyString): Pretty {
    const stack: { chunks: PrettyElem[], style: Style[] | Annotation }[] = [];
    let chunks: PrettyElem[] = [];
    let pos = 0;
    const unpack = (chunks: PrettyElem[]): Pretty =>
        chunks.length == 1 && typeof chunks[0] === 'string' ? chunks[0] : chunks;
    while (true) {
        const i = value.indexOf('\0', pos);
        if (i < 0) {
            chunks.push(value.substring(pos));
            if (stack.length) throw 'malformed pretty';
            return unpack(chunks);
        }
        chunks.push(value.substring(pos, i));
        const j = value.indexOf('\0', i + 1);
        if (j < 0) throw 'malformed pretty';
        if (i + 1 < j) {
            stack.push({ chunks, style: JSON.parse(value.substring(i + 1, j)) });
            chunks = [];
        } else {
            const child = stack.pop();
            if (!child) throw 'malformed pretty';
            child.chunks.push({ contents: unpack(chunks), style: child.style });
            chunks = child.chunks;
        }
        pos = j + 1;
    }
}

const escapeHtml = (s: string): string =>
    s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
        .replace(/'/g, '&#39;').replace(/"/g, '&quot;');

export function prettyStringToMarkdown(
    value: PrettyString,
    html: boolean = false, // html disabled because it looks like crap
): vscode.MarkdownString {
    const md = new vscode.MarkdownString;
    const pretty = parsePretty(value);
    if (typeof pretty === 'string') {
        md.appendCodeblock(pretty, 'hol4');
    } else {
        let result = '';
        function pushStyle(style: Style[] | Annotation): string {
            let after = '';
            const color = (c: string) => {
                result += `<span style="color:${c};">`;
                after = '</span>' + after;
            };
            switch (style) {
                // TODO: use sensible colors from the theme
                case 'FV': color('#008000'); break;
                case 'BV': color('#000080'); break;
                case 'TyV': color('#800080'); break;
                case 'TyOp': color('#8000C0'); break;
                case 'TySyn': color('#C00080'); break;
                case 'Const':
                case 'SymConst':
                case 'StringLit': color('#00A000'); break;
                case 'FldName': color('#00B000'); break;
                case 'NumLit': color('#300000'); break;
                case 'CharLit': color('#305000'); break;
                default:
                    if ('Note' in style) break;
                    for (const sty of style) {
                        switch (sty) {
                            case 'B': result += '<strong>'; after = '</strong>' + after; break;
                            case 'U': result += '<em>'; after = '</em>' + after; break;
                            default: {
                                if ('u' in sty) break;
                                if ('FG' in sty) { color(sty.FG); break; }
                                result += `<span style="background-color:${sty.BG};">'`;
                                after = '</span>' + after;
                            }
                        }
                    }
            }
            return after;
        }
        function pushPretty(p: Pretty) {
            if (typeof p === 'string') {
                result += html ? escapeHtml(p) : p;
            } else {
                for (const elem of p) {
                    if (typeof elem === 'string') {
                        result += html ? escapeHtml(elem) : elem;
                    } else {
                        let after = html ? pushStyle(elem.style) : '';
                        pushPretty(elem.contents);
                        result += after;
                    }
                }
            }
        }
        if (html) {
            md.supportHtml = true;
            md.isTrusted = true;
            result += '<code>';
            pushPretty(pretty);
            result += '</code>';
            md.value = result;
        } else {
            pushPretty(pretty);
            md.appendCodeblock(result, 'hol4');
        }

    }
    return md;
}
