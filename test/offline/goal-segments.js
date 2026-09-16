// The goals pane's type/identity tooltips, checked without VS Code.
//
// The goals pane is the one place hover cannot help: its text is in no
// file, so there is nothing to hover over.  The server sends `segments`
// beside `pretty` -- the same text, taken apart, each symbol carrying
// what it is.  These checks cover the two things that make that usable:
// what a tooltip says, and that the text still comes out intact.
//
// Nothing here needs an extension host; `vscode` is stubbed and the
// real compiled out/common.js is driven.  Run via `npm run
// test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

// common.ts imports vscode but only reaches for it inside functions
// these tests never call, and `GoalSegment` is a type-only import, so
// nothing is required at load beyond this.
const vscodeStub = {
  ViewColumn: { Beside: -2 },
  window: { createWebviewPanel: () => ({}) },
  workspace: { getConfiguration: () => ({ get: () => undefined }) },
  commands: { registerCommand: () => ({ dispose() {} }) },
};
const origResolve = Module._resolveFilename;
Module._resolveFilename = function (request, ...rest) {
  if (request === 'vscode') return 'vscode';
  return origResolve.call(this, request, ...rest);
};
const origLoad = Module._load;
Module._load = function (request, ...rest) {
  if (request === 'vscode') return vscodeStub;
  return origLoad.call(this, request, ...rest);
};

const { segmentTitle, segmentsToHtml, hitLocation, KIND_COLORS, KIND_CSS,
        contextLine, contextSkip } =
  require(path.join(REPO, 'out', 'common.js'));

let failed = 0;
function check(what, ok, got) {
  if (ok) { console.log('  ok   ' + what); }
  else { failed++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
}

console.log('goal-state segment tooltips');

// --- what a tooltip says ---------------------------------------------
check('a constant is named by theory and typed',
      segmentTitle({ text: 'MAP', kind: 'const', name: 'listTheory$MAP',
                     ty: "('a -> 'b) -> 'a list -> 'b list" })
        === "listTheory$MAP : ('a -> 'b) -> 'a list -> 'b list",
      segmentTitle({ text: 'MAP', kind: 'const', name: 'listTheory$MAP',
                     ty: "('a -> 'b) -> 'a list -> 'b list" }));

check("a free variable shows HOL's own name :type",
      segmentTitle({ text: 'l', kind: 'fv', ty: "l :'a list" })
        === "l :'a list",
      segmentTitle({ text: 'l', kind: 'fv', ty: "l :'a list" }));

check('a bound variable says so',
      segmentTitle({ text: 'h', kind: 'bv', ty: "h :'a" })
        === "bound h :'a",
      segmentTitle({ text: 'h', kind: 'bv', ty: "h :'a" }));

check('plain text has no tooltip',
      segmentTitle({ text: ' = ' }) === undefined,
      segmentTitle({ text: ' = ' }));

// --- and the text survives -------------------------------------------
const segs = [
  { text: 'f' , kind: 'const', name: 'my$f', ty: 'num -> num' },
  { text: ' ' },
  { text: 'x' , kind: 'fv', ty: 'x :num' },
  { text: ' = y' },
];
const html = segmentsToHtml(segs);
check('every annotated segment gets a title',
      (html.match(/title=/g) || []).length === 2, html);
check('and a class naming its kind',
      html.includes('class="hol-const"') && html.includes('class="hol-fv"'),
      html);
check('plain runs are left as bare text',
      html.includes('</span> <span'), html);
check('the text reads exactly as the state did',
      html.replace(/<[^>]*>/g, '') === 'f x = y',
      html.replace(/<[^>]*>/g, ''));

// A goal is full of `/\`, `<`, `>` and `"`; a tooltip carries a type
// that is too.  Both go through escapeHtml, or the pane breaks.
const nasty = segmentsToHtml([
  { text: 'a < b', kind: 'const', name: 'x$"<"', ty: "'a -> 'a -> bool" },
]);
check('segment text is html-escaped',
      nasty.includes('a &lt; b'), nasty);
check('and so is the title',
      nasty.includes('&quot;') && !nasty.includes('title="x$"<"'), nasty);

// --- and the colours say what HOL says -------------------------------
// Written out rather than derived, so an unintended edit to the table
// fails here.  See `KIND_COLORS` in common.ts for why a constant is
// left plain -- that is the case this pins.
const wanted = {
  const: 'var(--vscode-editor-foreground)',
  fv: 'var(--vscode-terminal-ansiBlue, #2472c8)',
  bv: 'var(--vscode-terminal-ansiGreen, #0dbc79)',
  tyvar: 'var(--vscode-terminal-ansiMagenta, #bc3fbc)',
  tyop: 'var(--vscode-terminal-ansiCyan, #11a8cd)',
  tysyn: 'var(--vscode-terminal-ansiCyan, #11a8cd)',
};
check("the palette is vt100_terminal's, a constant left plain",
      Object.keys(wanted).every(k => KIND_COLORS[k] === wanted[k]) &&
        Object.keys(KIND_COLORS).length === Object.keys(wanted).length,
      KIND_COLORS);
check('and every kind of it reaches the stylesheet',
      Object.entries(wanted).every(
        ([k, c]) => KIND_CSS.includes(`.hol-${k} { color: ${c}; }`)),
      KIND_CSS);

// --- the tag line is pinned, so the body must not repeat it --------
// `pretty` opens with the combinator tags, which the pane now shows in
// a head that does not scroll.  Left in the body they would appear
// twice whenever the state is short enough not to scroll at all.
check('tags become the line pretty opens with',
      contextLine(['branch 2 of 3 of THENL', 'inside >-'])
        === '[branch 2 of 3 of THENL] [inside >-]',
      contextLine(['branch 2 of 3 of THENL', 'inside >-']));
check('no tags, no line',
      contextLine([]) === undefined && contextLine(undefined) === undefined,
      [contextLine([]), contextLine(undefined)]);

check('the skip covers the tag line and the blanks after it',
      contextSkip('[inside >-]\n\n!x. P x', ['inside >-']) === 13,
      contextSkip('[inside >-]\n\n!x. P x', ['inside >-']));
check('and nothing when the text does not open with it',
      contextSkip('!x. P x', ['inside >-']) === 0,
      contextSkip('!x. P x', ['inside >-']));
// A goal may itself begin with a `[`; only the tags the server sent
// are removed, never a bracket that looks like them.
check('a goal starting with a bracket is left alone',
      contextSkip('[1,2] = l', undefined) === 0,
      contextSkip('[1,2] = l', undefined));
check('leading blank lines go even with no tags',
      contextSkip('\n\n!x. P x', undefined) === 2,
      contextSkip('\n\n!x. P x', undefined));

// The skip is in characters of the concatenated text, so it can land
// inside a segment: that one keeps its tail and its tooltip.
const skipped = segmentsToHtml([
  { text: '[inside >-]\n\n' },
  { text: 'MAP', kind: 'const', name: 'listTheory$MAP', ty: 'num' },
], 13);
check('segments the skip covers are dropped whole',
      !skipped.includes('inside'), skipped);
check('and what is left keeps its annotation',
      skipped.includes('class="hol-const"') && skipped.includes('MAP'),
      skipped);
const straddled = segmentsToHtml(
  [{ text: 'abcdef', kind: 'fv', ty: 'x :num' }], 4);
check('a segment the skip lands inside keeps its tail',
      straddled.replace(/<[^>]*>/g, '') === 'ef', straddled);

// --- search hits say where they were proved -------------------------
check('a hit shows its script and line, not its path',
      hitLocation('file:///hol/src/finite_map/finite_mapScript.sml', 1234)
        === 'finite_mapScript.sml:1234',
      hitLocation('file:///hol/src/finite_map/finite_mapScript.sml', 1234));
check('a hit HOL records no location for shows nothing',
      hitLocation(undefined, 12) === undefined, hitLocation(undefined, 12));
check('and one with no line still names the script',
      hitLocation('file:///a/bScript.sml') === 'bScript.sml',
      hitLocation('file:///a/bScript.sml'));

console.log(failed === 0 ? '\nall checks passed'
                         : `\n${failed} check(s) failed`);
process.exit(failed === 0 ? 0 : 1);
