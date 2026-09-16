import { DocumentSelector, OutputChannel, window, workspace } from 'vscode';
import type { GoalSegment } from './lspClient';
export const EXTENSION_ID = 'oskarabrahamsson.hol4-mode';
export const KERNEL_ID = 'hol4';

export const hol4selector: DocumentSelector = [
    { scheme: 'file', language: KERNEL_ID },
    { scheme: 'untitled', language: KERNEL_ID }
];

let stderrOutput: OutputChannel;
let firstError = true;

/** Log a message with the 'hol-mode' prefix. */
export function log(message: string): void {
    stderrOutput = stderrOutput || window.createOutputChannel('HOL: Editor');
    stderrOutput.appendLine(message);
    // console.log(`--- hol-mode: ${message}`);
}

/** Log an error with the 'hol-mode' prefix. */
export function error(message: string): void {
    stderrOutput = stderrOutput || window.createOutputChannel('HOL: Editor');
    stderrOutput.appendLine(`Error: ${message}`);
    if (firstError) {
        stderrOutput.show(true);
        firstError = false;
    }
    // console.error(`!!! hol-mode: Error: ${message}`);
}

export function holdir(): string | undefined {
    return workspace.getConfiguration('hol4-mode').get<string>('holdir');
}

/** Execute an async fn such that any concurrent calls block until the previous calls finish. */
export function disallowConcurrency<T>(fn: (arg: T) => Promise<void>): (arg: T) => Promise<void> {
    let inprogressPromise = Promise.resolve()
    return (arg) => {
        inprogressPromise = inprogressPromise.then(() => fn(arg))
        return inprogressPromise
    }
};

export function partitionPoint(len: number, pred: (i: number) => boolean) {
    let start = 0;
    while (0 < len) {
        const half = len / 2 | 0;
        const middle = start + half;
        if (pred(middle)) {
            start = middle + 1;
            len -= half + 1;
        } else {
            len = half;
        }
    }
    return start;
}

export function pluralize(n: number, stem: string, s: string = 's') {
    return `${n} ${n == 1 ? stem : stem + s}`;
}

/* String escapers.  `escapeMLString' builds SML string literals for
 * the session's `use'/request traffic; `escapeHtml' is for the goals
 * webview.  They lived in a `server.ts' whose server is gone. */
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

export const escapeHtml = (s: string): string =>
    s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
        .replace(/'/g, '&#39;').replace(/"/g, '&quot;');

/** What to say about a segment on hover, or undefined if it says
 * nothing.  A constant's theory-qualified name is the identity
 * question worth answering; a variable's `ty` is already HOL's own
 * `name :type`, so it needs no second copy of the name. */
export function segmentTitle(seg: GoalSegment): string | undefined {
    if (!seg.kind) return undefined;
    if (seg.name && seg.ty) return `${seg.name} : ${seg.ty}`;
    if (seg.name) return seg.name;
    if (seg.ty) return seg.kind === 'bv' ? `bound ${seg.ty}` : seg.ty;
    return undefined;
}

/** The server's combinator tags as the single bracketed line that
 * `pretty` opens with, or undefined when there are none.  The tags
 * arrive separately -- `goalFrag`'s `context_lines` is exposed, in its
 * own words, "so a client can pin them somewhere that does not scroll
 * away" -- so the line to remove from `pretty` is known exactly rather
 * than guessed at: a goal can itself begin with a `[`. */
export function contextLine(ctx?: string[]): string | undefined {
    if (!ctx || ctx.length === 0) return undefined;
    return ctx.map((c) => `[${c}]`).join(' ');
}

/** How much of `text` is the prefix a pinned header makes redundant:
 * the tag line, when `text` opens with it, and the blank lines after
 * it.  Only newlines go -- the goal block's own indentation is
 * load-bearing. */
export function contextSkip(text: string, ctx?: string[]): number {
    const line = contextLine(ctx);
    let n = line !== undefined && text.startsWith(line) ? line.length : 0;
    while (text[n] === '\n') n++;
    return n;
}

/** What each kind of symbol is coloured, held equal to the colours
 * `PPBackEnd.vt100_terminal` gives the same goal in a terminal: fv
 * Blue, bv Green, tyv Purple, tyop and tysyn BlueGreen.  The theme's
 * own terminal colours, so HOL's hex is only the fallback.
 *
 * A constant takes the body's own foreground, because HOL gives it no
 * colour either: `output_colors` has no field for a constant, and
 * `add_xstring` lets one fall through to plain text.  Colouring it
 * said something about it that HOL does not say, and said it in the
 * free variables' blue.
 *
 * Hue only.  `Blue` is a light colour, so `fg_to_vt100` sends it as
 * `;1;34` and the `pretty` fallback path renders a free variable bold
 * through `.ansi-bold`; this path leaves the weight alone. */
export const KIND_COLORS: Record<NonNullable<GoalSegment['kind']>, string> = {
    const: 'var(--vscode-editor-foreground)',
    fv: 'var(--vscode-terminal-ansiBlue, #2472c8)',
    bv: 'var(--vscode-terminal-ansiGreen, #0dbc79)',
    tyvar: 'var(--vscode-terminal-ansiMagenta, #bc3fbc)',
    tyop: 'var(--vscode-terminal-ansiCyan, #11a8cd)',
    tysyn: 'var(--vscode-terminal-ansiCyan, #11a8cd)',
};

/** `KIND_COLORS` as the stylesheet rules for the classes
 * `segmentsToHtml` puts on.  Constant, so built once. */
export const KIND_CSS: string =
    Object.entries(KIND_COLORS)
        .map(([kind, color]) => `  .hol-${kind} { color: ${color}; }`)
        .join('\n');

/** Render the segments as HTML, giving each annotated one a `title`
 * so the browser shows it as a tooltip, and the same class
 * `ansiToHtml` would have derived from the colour -- the kind is what
 * the colour was standing for. */
export function segmentsToHtml(segs: GoalSegment[], skip = 0): string {
    let out = '';
    // `skip` counts characters of the concatenated text, so it can fall
    // in the middle of a segment: drop the ones it covers whole and
    // take the tail of the one it lands in.
    let seen = 0;
    for (const seg of segs) {
        const raw = seg.text ?? '';
        const from = Math.min(Math.max(skip - seen, 0), raw.length);
        seen += raw.length;
        if (raw.length > 0 && from === raw.length) continue;
        const text = escapeHtml(raw.slice(from));
        const title = segmentTitle(seg);
        if (title === undefined) {
            out += text;
        } else {
            const cls = seg.kind ? ` class="hol-${seg.kind}"` : '';
            out += `<span${cls} title="${escapeHtml(title)}">${text}</span>`;
        }
    }
    return out;
}

/** Where a search hit was proved, as a reader wants it: the script's
 * own name and the line, not the whole path.  One per result, the
 * paths would crowd out the theorems -- and the path is what the
 * *opening* needs, not the reading. */
export function hitLocation(uri?: string, line?: number): string | undefined {
    if (!uri) return undefined;
    const name = uri.split('/').pop() ?? uri;
    return line === undefined ? name : `${name}:${line}`;
}
