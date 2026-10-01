// Typing HOL the way HOL is written.
//
// Emacs users of HOL do not type `\and` to get `∧`; they type `/\`, and
// the quail input method in `tools/editor-modes/emacs/hol-input.el`
// turns it into `∧` as they go.  The eleven rules at the bottom of that
// file (lines 1131-1142) are the whole vocabulary, and they are
// reproduced verbatim below.
//
// Two of them exist only as escape hatches: `!!` gives back a literal
// `!` and `??` a literal `?`, which is how you write a HOL `!` once `!`
// has come to mean `∀`.
//
// Nothing here imports `vscode`.  The context test is injected, so the
// machine can be driven over a plain string in a plain node test.
import { Ctx } from './holContext';

/**
 * The eleven leaderless rules, from `hol-input.el:1131-1142`.
 *
 * These are a separate namespace from the `\`-leader table in
 * `unicode-completions.json`, not a subset of it: there `!!` is `‼` and
 * `?!` is `‽`, which is not what HOL means by them.
 */
export const BUILTIN_RULES: Readonly<Record<string, string>> = {
    '/\\': '∧',
    '\\/': '∨',
    '==>': '⇒',
    '<=>': '⇔',
    '<>': '≠',
    '<=': '≤',
    '!': '∀',
    '?': '∃',
    '?!': '∃!',
    '!!': '!',
    '??': '?',
};

/** A rule table with the prefix relations precomputed. */
export interface CompiledRules {
    /** The replacement for an exact key, if there is one. */
    get(key: string): string | undefined;
    /** Is `key` a prefix -- proper or not -- of some rule? */
    isPrefix(key: string): boolean;
    /** Does some rule strictly extend `key`? */
    extendable(key: string): boolean;
    /**
     * The longest proper suffix of `key` that is still a live prefix.
     * This is quail's MAXIMUM-SHORTEST: after a dead end the tail of
     * what was typed may still start a rule, so `<<=` has to give `<≤`
     * rather than giving up on the whole run.
     */
    failureLink(key: string): string;
}

/**
 * Merge user rules over the built-ins and precompute the prefix sets.
 *
 * A `null` value removes a built-in.  The relations are derived from the
 * merged table rather than hardcoded, because adding `==` alongside the
 * built-in `==>` creates a new ambiguity that the machine has to honour.
 */
export function compileRules(user?: Record<string, string | null>): CompiledRules {
    const map = new Map<string, string>(Object.entries(BUILTIN_RULES));
    for (const [k, v] of Object.entries(user ?? {})) {
        if (v === null || v === '') { map.delete(k); } else { map.set(k, v); }
    }
    const prefixes = new Set<string>();
    for (const k of map.keys()) {
        for (let i = 1; i <= k.length; i++) { prefixes.add(k.slice(0, i)); }
    }
    const extendables = new Set<string>();
    for (const k of map.keys()) {
        for (let i = 1; i < k.length; i++) { extendables.add(k.slice(0, i)); }
    }
    return {
        get: (k) => map.get(k),
        isPrefix: (k) => prefixes.has(k),
        extendable: (k) => extendables.has(k),
        failureLink: (k) => {
            for (let i = 1; i < k.length; i++) {
                const s = k.slice(i);
                if (prefixes.has(s)) { return s; }
            }
            return '';
        },
    };
}

/** An edit to apply to the document. */
export interface Edit {
    offset: number;
    length: number;
    newText: string;
    cursorOffset?: number;
}

/** What one keystroke did. */
export interface Step {
    /** The rewrite to apply, if a rule fired. */
    edit?: Edit;
    /**
     * True when this keystroke completed a rule whose last character is
     * the leader.  The leader rewriter must not start tracking an
     * abbreviation for it -- `/\` is `∧`, not the start of `\and`.
     */
    suppressLeaderStart: boolean;
    /**
     * Set when the fired rule swallowed a leader that the leader
     * rewriter has already started tracking, as in `\` then `/`.  Any
     * tracked abbreviation overlapping this range must be dropped before
     * the edit lands, or it will point at text that no longer exists.
     */
    cancelLeaderOver?: { offset: number; length: number };
    /** The range to underline, if a rule is provisionally committed. */
    pending?: { offset: number; length: number };
}

const NO_STEP: Step = { suppressLeaderStart: false };

type State =
    | { kind: 'idle' }
    // ASCII still in the document; a live prefix but not yet a rule, or
    // a rule we declined to commit because the context was wrong.
    | { kind: 'partial'; key: string; offset: number }
    // `symbol` has been written over the ASCII at `offset`; `key` is a
    // rule, and something strictly extends it, so it may yet be retracted.
    | { kind: 'provisional'; key: string; symbol: string; offset: number };

/**
 * The input method, as a state machine over single-character inserts.
 *
 * It commits provisionally rather than deferring, which is what quail
 * does: typing `!` writes `∀` immediately, and a second `!` *retracts*
 * that and writes `!`.  The alternative -- holding the ASCII back until
 * the next keystroke disambiguates -- shows you ASCII where you expect
 * Unicode, and makes every non-extending keystroke cost an edit.  Here,
 * finalising is free: the document is already right.
 */
export class InputMachine {
    private state: State = { kind: 'idle' };

    constructor(
        private readonly rules: CompiledRules,
        private readonly classify: (offset: number) => Ctx
    ) { }

    reset(): void { this.state = { kind: 'idle' }; }

    /** The range currently underlined, if any. */
    pending(): { offset: number; length: number } | undefined {
        const s = this.state;
        if (s.kind === 'provisional') {
            return { offset: s.offset, length: s.symbol.length };
        }
        return undefined;
    }

    /** Shift state to account for an edit made before us by someone else. */
    shift(delta: number): void {
        const s = this.state;
        if (s.kind !== 'idle') { s.offset += delta; }
    }

    /**
     * Feed one inserted character. `offset` is where it was inserted, so
     * the cursor is now at `offset + 1`.
     */
    insert(offset: number, ch: string): Step {
        const s = this.state;

        // A cursor that jumped is a cursor that abandoned whatever was
        // pending.  A provisional is already correct in the document, so
        // abandoning it costs nothing.
        if (s.kind === 'provisional' && offset !== s.offset + s.symbol.length) {
            this.state = { kind: 'idle' };
        } else if (s.kind === 'partial' && offset !== s.offset + s.key.length) {
            this.state = { kind: 'idle' };
        }

        return this.step(offset, ch, true);
    }

    private step(offset: number, ch: string, mayRetry: boolean): Step {
        const s = this.state;
        const key = (s.kind === 'idle' ? '' : s.key) + ch;

        if (this.rules.isPrefix(key)) {
            const symbol = this.rules.get(key);
            if (symbol === undefined) {
                // A live prefix with no translation of its own: leave the
                // ASCII alone and wait.
                const start = s.kind === 'idle' ? offset : s.offset;
                this.state = { kind: 'partial', key, offset: start };
                return { suppressLeaderStart: false, pending: undefined };
            }
            return this.commit(offset, key, symbol, s);
        }

        // Dead end.
        if (s.kind === 'provisional') {
            // The ASCII that led here is gone, replaced by the symbol, so
            // the only thing left to retry is the character just typed.
            this.state = { kind: 'idle' };
            return mayRetry ? this.step(offset, ch, false) : NO_STEP;
        }

        if (s.kind === 'partial') {
            // MAXIMUM-SHORTEST: back off to the longest suffix that is
            // still live and try again from there.
            const link = this.rules.failureLink(key);
            this.state = link === ''
                ? { kind: 'idle' }
                : { kind: 'partial', key: link.slice(0, -1), offset: offset - link.length + 1 };
            if (link === '') { return NO_STEP; }
            return mayRetry ? this.step(offset, ch, false) : NO_STEP;
        }

        this.state = { kind: 'idle' };
        return NO_STEP;
    }

    private commit(offset: number, key: string, symbol: string, s: State): Step {
        // Where the text being replaced starts.  For a provisional the
        // ASCII is already gone, so we are overwriting the symbol.
        const start = s.kind === 'provisional'
            ? s.offset
            : (s.kind === 'partial' ? s.offset : offset);
        const length = s.kind === 'provisional'
            ? s.symbol.length + 1          // the symbol, plus the char just typed
            : key.length;

        if (this.classify(start) !== 'term') {
            // Right shape, wrong place.  Keep tracking -- the user may be
            // about to type their way into a quotation -- but change nothing.
            this.state = { kind: 'partial', key, offset: start };
            return NO_STEP;
        }

        const cursorMark = symbol.indexOf('$CURSOR');
        const newText = symbol.replace('$CURSOR', '');

        const step: Step = {
            edit: {
                offset: start,
                length,
                newText,
                cursorOffset: cursorMark === -1 ? undefined : cursorMark,
            },
            suppressLeaderStart: false,
        };

        // The leader rewriter has to be told about the backslashes we
        // just ate.  `/\` ends with one, so it is about to start tracking
        // an abbreviation that our edit deletes; `\/` began with one, so
        // it is already tracking.
        if (key.endsWith('\\')) { step.suppressLeaderStart = true; }
        if (key.includes('\\') && !key.endsWith('\\')) {
            step.cancelLeaderOver = { offset: start, length };
        }

        if (this.rules.extendable(key)) {
            this.state = { kind: 'provisional', key, symbol: newText, offset: start };
            step.pending = { offset: start, length: newText.length };
        } else {
            this.state = { kind: 'idle' };
        }
        return step;
    }
}

/** What pressing `` ` `` should do. */
export type QuoteAction =
    | { kind: 'literal' }
    | { kind: 'move'; to: number }
    | { kind: 'edits'; edits: Edit[]; cursor: number };

const OPEN_FOR: Record<string, string> = { '’': '‘', '”': '“' };
const OTHER_OPEN: Record<string, string> = { '‘': '“', '“': '‘' };
const OTHER_CLOSE: Record<string, string> = { '’': '”', '”': '’' };
const CLOSE_FOR: Record<string, string> = { '‘': '’', '“': '”' };

/**
 * Smart insertion of the Unicode term-quotation delimiters, ported from
 * `holscript-dbl-backquote` in
 * `tools/editor-modes/emacs/holscript-mode.el:105-156`.
 *
 * HOL writes terms as `‘…’` and types as `“…”`, and neither is on a
 * keyboard.  Emacs binds the backtick key to this, so one press gives
 * you the pair and a second turns a single-quoted pair into a
 * double-quoted one.  The three further cases -- stepping over a closing
 * delimiter, retyping an existing quotation, wrapping a selection --
 * are what stops the key from being merely an insert.
 */
export function smartQuote(
    text: string,
    selStart: number,
    selEnd: number,
    classify: (offset: number) => Ctx
): QuoteAction {
    // Inside a string literal, or inside an embedded language that is
    // not HOL, a backtick is just a backtick.
    const ctx = classify(selStart);
    if (ctx === 'string' || ctx === 'foreign') { return { kind: 'literal' }; }

    // A selection gets wrapped rather than replaced.
    if (selStart !== selEnd) {
        return {
            kind: 'edits',
            edits: [
                { offset: selEnd, length: 0, newText: '’' },
                { offset: selStart, length: 0, newText: '‘' },
            ],
            cursor: selStart + 1,
        };
    }

    const at = text[selStart];
    const before = selStart > 0 ? text[selStart - 1] : '';

    // On a closing delimiter: if the pair is empty, swap it for the
    // other kind; otherwise step over it.
    if (at === '’' || at === '”') {
        if (before === OPEN_FOR[at]) {
            const open = OTHER_OPEN[before];
            return {
                kind: 'edits',
                edits: [{
                    offset: selStart - 1, length: 2,
                    newText: open + CLOSE_FOR[open],
                }],
                cursor: selStart,
            };
        }
        return { kind: 'move', to: selStart + 1 };
    }

    // On an opening delimiter of a non-empty quotation: retype both ends.
    if (at === '‘' || at === '“') {
        const close = CLOSE_FOR[at];
        const partner = findPartner(text, selStart, at, close);
        if (partner === -1) { return { kind: 'literal' }; }
        return {
            kind: 'edits',
            edits: [
                { offset: partner, length: 1, newText: OTHER_CLOSE[close] },
                { offset: selStart, length: 1, newText: OTHER_OPEN[at] },
            ],
            // Emacs ends a retype sitting on the delimiter it just
            // changed, rather than past it.
            cursor: selStart,
        };
    }

    return {
        kind: 'edits',
        edits: [{ offset: selStart, length: 0, newText: '‘’' }],
        cursor: selStart + 1,
    };
}

/**
 * The closing delimiter matching the one at `open`, or -1.
 *
 * Emacs refuses the retype when it meets another opening delimiter
 * first, and so do we: that means the quotation is unbalanced, and
 * rewriting one end of it would make things worse rather than better.
 */
function findPartner(text: string, open: number, openCh: string, closeCh: string): number {
    for (let i = open + 1; i < text.length; i++) {
        if (text[i] === closeCh) { return i; }
        if (text[i] === openCh) { return -1; }
    }
    return -1;
}
