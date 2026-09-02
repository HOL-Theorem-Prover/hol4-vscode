import { DocumentSelector, OutputChannel, window, workspace } from 'vscode';
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
