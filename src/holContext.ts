// Where, in a HOL script, is the text actually HOL?
//
// A `*Script.sml` file is SML with HOL term syntax embedded in it, and
// the two want opposite things from an input method.  Inside a term,
// `!` means `∀` and `<=` means `≤`.  Twenty lines away, in the SML that
// surrounds it, `!` dereferences a ref and `<=` compares two numbers --
// rewriting either would be vandalism.  So before any ASCII-to-Unicode
// rule fires, something has to say which of the two the cursor is in.
//
// That is this module.  It is a single forward scan with no `vscode`
// import, so it can be driven from a plain node test.
//
// The regions come from two places that already know the answer:
// `hol4-grammar.json` in this repo, whose `#hol-term` rule marks the
// blocks whose bodies are terms, and HOL's own lexer,
// `tools/parsing/HolLex`, which is the authority where the two
// disagree.
/**
 * What the text at an offset is.  Only `'term'` is HOL term syntax;
 * `'foreign'` is an embedded language that is deliberately none of our
 * business.
 */
export type Ctx = 'term' | 'sml' | 'foreign' | 'string' | 'comment';

// Which kind of block the line-anchored keywords have put us in.
// 'none' is the top level, which is ordinary SML.
type Block = 'none' | 'term' | 'sml' | 'foreign';

// A term quotation we are inside.  Backtick quotations carry their
// width: `HolLex`'s `quotebegin`/`fullquotebegin` pair n backticks with
// n backticks, so ``x`` closes only on another ``.
type Quote =
    | { kind: 'single' }            // ‘ … ’
    | { kind: 'double' }            // “ … ”
    | { kind: 'ticks', n: number }; // `ⁿ … `ⁿ

// Block openers, anchored at the start of a line.  `HolLex` matches
// these with `{ws}`, which is spaces and tabs but not newlines, so the
// colon has to be on the same line as the keyword.
//
// `Theorem foo :` opens a term; `Theorem foo =` (HolLex:348,
// `BeginSimpleThm`) is an SML expression and is deliberately absent
// here, so it falls through to the top level.
const OPENERS: [RegExp, Block][] = [
    [/(?:Theorem|Triviality)[ \t]+[A-Za-z0-9_']*(?:\[[^\]]*\])?[ \t]*:/y, 'term'],
    [/Definition[ \t]+[A-Za-z0-9_']*(?:\[[^\]]*\])?[ \t]*:/y, 'term'],
    [/Datatype[ \t]*:/y, 'term'],
    [/(?:Co)?Inductive[ \t]+[A-Za-z0-9_']*[ \t]*:/y, 'term'],
    // `Quote <parser> :` and `Quote <id> = <parser> :` (HolLex:251-252).
    // The qualified id names the parser the body is handed to, so the
    // body is an arbitrary embedded language -- CakeML, say -- and HOL's
    // Unicode has no business there.  Hence 'foreign' rather than
    // 'term', even though this block shares `parseQuoteEndDef` with
    // Definition and Inductive, which are terms.
    [/Quote[ \t]+[A-Za-z0-9_'.]+[ \t]*(?:=[ \t]*[A-Za-z0-9_'.]+[ \t]*)?:/y, 'foreign'],
    [/Proof\b/y, 'sml'],
    [/Termination\b/y, 'sml'],
    [/End\b/y, 'none'],
    [/QED\b/y, 'none'],
];

/**
 * What kind of text sits at `offset`.
 *
 * Costs a scan from the start of `text`: 1.8 ms on the largest script in
 * HOL (`src/probability/lebesgueScript.sml`, 510 KB), 0.6 ms on a
 * typical one.  Callers that ask repeatedly should memoise on the
 * document version.
 */
export function classifyOffset(text: string, offset: number): Ctx {
    let block: Block = 'none';
    let quote: Quote | undefined;
    let inString = false;
    let commentDepth = 0;
    let antiqDepth = 0; // inside ^( … ), which is SML again

    const end = Math.max(0, Math.min(offset, text.length));

    for (let i = 0; i < end; i++) {
        const c = text[i];

        // A block keyword only counts at the start of a line, and only
        // when nothing else is open -- otherwise `End` in a comment or a
        // string would close the block.
        if ((i === 0 || text[i - 1] === '\n') &&
            !inString && commentDepth === 0 && !quote && antiqDepth === 0) {
            for (const [re, target] of OPENERS) {
                re.lastIndex = i;
                if (re.test(text)) { block = target; break; }
            }
        }

        // A foreign block is opaque: we track nothing inside it beyond
        // looking for the `End` that closes it.
        if (block === 'foreign') { continue; }

        if (inString) {
            if (c === '\\') { i++; } else if (c === '"') { inString = false; }
            continue;
        }
        if (commentDepth > 0) {
            if (c === '(' && text[i + 1] === '*') { commentDepth++; i++; }
            else if (c === '*' && text[i + 1] === ')') { commentDepth--; i++; }
            continue;
        }
        if (c === '(' && text[i + 1] === '*') { commentDepth = 1; i++; continue; }
        if (c === '"') { inString = true; continue; }

        if (antiqDepth > 0) {
            if (c === '(') { antiqDepth++; }
            else if (c === ')') { antiqDepth--; }
            continue;
        }

        if (quote) {
            // An antiquotation drops back into SML for the length of the
            // parenthesised expression.  Only the `^(…)` form is tracked;
            // `^ident` is left alone because an identifier cannot contain
            // anything we would rewrite.
            if (c === '^' && text[i + 1] === '(') { antiqDepth = 1; i++; continue; }
            if (quote.kind === 'single' && c === '’') { quote = undefined; }
            else if (quote.kind === 'double' && c === '”') { quote = undefined; }
            else if (quote.kind === 'ticks' && c === '`') {
                let n = 0;
                while (text[i + n] === '`') { n++; }
                if (n === quote.n) { quote = undefined; }
                i += n - 1;
            }
            continue;
        }

        if (c === '‘') { quote = { kind: 'single' }; }
        else if (c === '“') { quote = { kind: 'double' }; }
        else if (c === '`') {
            let n = 0;
            while (text[i + n] === '`') { n++; }
            quote = { kind: 'ticks', n };
            i += n - 1;
        }
    }

    if (block === 'foreign') { return 'foreign'; }
    if (inString) { return 'string'; }
    if (commentDepth > 0) { return 'comment'; }
    if (antiqDepth > 0) { return 'sml'; }
    if (quote) { return 'term'; }
    return block === 'term' ? 'term' : 'sml';
}
