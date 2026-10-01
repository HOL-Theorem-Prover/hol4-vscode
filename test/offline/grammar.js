// What the syntax highlighter makes of a HOL script.
//
// The checks that matter here are not "is Theorem a keyword" -- that has
// always worked -- but the ones about *recovery*.  A TextMate grammar
// has no error handling: a rule that runs past a closing delimiter keeps
// running to the end of the file, and the symptom shows up hundreds of
// lines away as keywords that have quietly stopped being keywords.  Most
// of this file is regression cases for that failure mode.
//
// Scopes are computed by test/offline/textmate.js, a small stand-in for
// vscode-textmate, which is not a dependency of this extension.  Run via
// `npm run test:offline`.
const path = require('path');
const REPO = path.join(__dirname, '..', '..');
const { tokenize, scopesOf, load } = require(path.join(__dirname, 'textmate.js'));

const grammar = load(path.join(REPO, 'hol4-grammar.json'));

let failed = 0;
function check(what, ok, got) {
  if (ok) { console.log('  ok   ' + what); }
  else { failed++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
}

/** Assert the scope of `word` on line `line` of `src` starts with `want`. */
function scope(what, src, line, word, want) {
  const tok = tokenize(grammar, src);
  const got = (scopesOf(tok, line, word) || []).filter((s) => s !== 'source.hol4');
  check(what, got.some((s) => s.startsWith(want)), got);
}

console.log('the keywords that open and close a block');
const BLOCKS = [
  ['Theorem', 'Theorem t:\n  x\nProof\n  rw[]\nQED\n', [[0, 'Theorem'], [2, 'Proof'], [4, 'QED']]],
  ['Definition', 'Definition f:\n  f x = x\nEnd\n', [[0, 'Definition'], [2, 'End']]],
  ['Datatype', 'Datatype:\n  t = L | N\nEnd\n', [[0, 'Datatype'], [2, 'End']]],
  ['Inductive', 'Inductive r:\n  r 0\nEnd\n', [[0, 'Inductive'], [2, 'End']]],
  ['Termination', 'Definition f:\n  f x = f x\nTermination\n  WF_REL_TAC `$<`\nEnd\n',
    [[0, 'Definition'], [2, 'Termination'], [4, 'End']]],
];
for (const [name, src, spots] of BLOCKS) {
  for (const [line, word] of spots) {
    scope(name + ': ' + word, src, line, word, 'keyword');
  }
}

console.log('\nthe script header');
const HEADER = 'Theory ninetyOne\nAncestors\n  prim_rec arithmetic\nLibs\n  Defn TotalDefn\n\nval x = 1;\n';
scope('Theory', HEADER, 0, 'Theory', 'keyword.other.block');
scope('the theory name', HEADER, 0, 'ninetyOne', 'entity.name.theory');
scope('Ancestors', HEADER, 1, 'Ancestors', 'keyword.other.block');
scope('Libs', HEADER, 3, 'Libs', 'keyword.other.block');
scope('Theory with an attribute',
      'Theory suspSibB[bare]\nAncestors suspSibA\n', 0, 'Theory', 'keyword.other.block');
scope('Ancestors with names on the same line',
      'Theory t\nAncestors suspSibA\n', 1, 'Ancestors', 'keyword.other.block');
scope('Ancestors with an attribute',
      'Theory t\nAncestors[qualified]\n  arithmetic\n', 1, 'Ancestors', 'keyword.other.block');
scope('a header does not swallow what follows',
      HEADER, 6, 'val', 'keyword.other.reserved');

console.log('\nthe suspend/resume forms');
const RESUME = 'Theory t\n\nResume willsplit[q]:\n  RES_TAC\nQED\n\nFinalise willsplit\n';
scope('Resume', RESUME, 2, 'Resume', 'keyword.other.block');
scope('its QED', RESUME, 4, 'QED', 'keyword.other.block');
scope('Finalise', RESUME, 6, 'Finalise', 'keyword.other.block');

console.log('\nQuote blocks');
const QUOTE = 'Quote cml = cakeml:\n  fun g x = if x <= 0 then ! else x;\nEnd\n\nTheorem t:\n  x\nProof\n  rw[]\nQED\n';
scope('Quote', QUOTE, 0, 'Quote', 'keyword.other.block');
scope('its End', QUOTE, 2, 'End', 'keyword.other.block');
scope('and the theorem after it is unaffected', QUOTE, 4, 'Theorem', 'keyword.other.block');

console.log('\na rule must not run past a closing delimiter');
{
  // `!` opens a HOL binder, whose variable list used to be `[^.]+` -- so
  // in a tactic like this it ran to the `.` of `Q.SPECL`, eating the
  // closing backtick on the way.  The quotation then never closed and
  // every keyword below it stopped being a keyword, for the rest of the
  // file.  Seen in src/pred_set/src/pred_setScript.sml.
  const src = 'Theorem t:\n  x\nProof\n' +
              'Q.PAT_X_ASSUM `$! m` (MP_TAC o Q.SPECL [`t DELETE f e`, `f`]) THEN\n' +
              '  rw[]\nQED\n\nTheorem later:\n  y\nProof\n  rw[]\nQED\n';
  scope('the QED after a binder in a tactic quotation', src, 5, 'QED', 'keyword.other.block');
  scope('and a theorem far below it', src, 7, 'Theorem', 'keyword.other.block');
}
{
  const src = 'Theorem t:\n  !x. P x\nProof\n  rw[]\nQED\n';
  scope('a binder inside a theorem statement still highlights', src, 1, '!', 'keyword.other.binder');
  scope('and the statement still ends at Proof', src, 2, 'Proof', 'keyword.other.block');
}
{
  // `end` matches n backticks against n backticks via a backreference.
  const src = 'val x = ``a /\\ b``;\nTheorem t:\n  x\nProof\n  rw[]\nQED\n';
  scope('a double-backtick quotation closes', src, 5, 'QED', 'keyword.other.block');
}
{
  // SML string continuation: the backslash pairs with the newline.
  const src = 'val s = "line one\\\n\\ line two";\nTheorem t:\n  x\nProof\n  rw[]\nQED\n';
  scope('a continued string closes', src, 6, 'QED', 'keyword.other.block');
}

console.log('\nspacing and comments');
scope('Datatype tolerates a space before the colon',
      'Datatype : (* extreal_TY_DEF *)\n  t = L | N\nEnd\n', 2, 'End', 'keyword.other.block');
{
  const src = 'Theorem t:\n  x\nProof\n  rw[]\nQED\n\n(*\nDefinition f:\n  f x = x\nEnd\n*)\n';
  const tok = tokenize(grammar, src);
  const got = (scopesOf(tok, 9, 'End') || []).filter((s) => s !== 'source.hol4');
  check('End inside a comment is a comment, not a keyword',
        got.some((s) => s.startsWith('comment')) && !got.some((s) => s.startsWith('keyword')), got);
}

console.log('\nevery block keyword carries one and the same scope');
{
  // A theme colours by scope.  While `Theorem` was
  // `keyword.other.theorem.hol` and the `End` closing a Datatype was
  // `keyword.other.datatype-end.hol`, any theme with a rule more
  // specific than `keyword` could render them in different shades --
  // which is exactly what was reported.  One scope, one colour.
  const src = [
    'Theory t', 'Ancestors', '  arithmetic', 'Libs', '  bossLib', '',
    'Definition f:', '  f x = x', 'End', '',
    'Datatype:', '  u = L', 'End', '',
    'Inductive r:', '  r 0', 'End', '',
    'Quote cml = cakeml:', '  x', 'End', '',
    'Resume w[q]:', '  RES_TAC', 'QED', '',
    'Finalise w', '',
    'Theorem a:', '  x', 'Proof', '  rw[]', 'QED', '',
    'Definition g:', '  g x = x', 'Termination', '  WF_REL_TAC `$<`', 'End',
  ].join('\n');
  const tok = tokenize(grammar, src);
  const spots = [
    [0, 'Theory'], [1, 'Ancestors'], [3, 'Libs'],
    [6, 'Definition'], [8, 'End'],
    [10, 'Datatype'], [12, 'End'],
    [14, 'Inductive'], [16, 'End'],
    [18, 'Quote'], [20, 'End'],
    [22, 'Resume'], [24, 'QED'],
    [26, 'Finalise'],
    [28, 'Theorem'], [30, 'Proof'], [32, 'QED'],
    [34, 'Definition'], [36, 'Termination'], [38, 'End'],
  ];
  const seen = new Map();
  for (const [line, word] of spots) {
    const got = (scopesOf(tok, line, word) || []).filter((s) => s !== 'source.hol4');
    seen.set(word + '@' + line, got.join(' '));
  }
  const distinct = [...new Set(seen.values())];
  check('all ' + spots.length + ' of them share one scope',
        distinct.length === 1 && distinct[0] === 'keyword.other.block.hol',
        distinct);
  const odd = [...seen.entries()].filter(([, v]) => v !== 'keyword.other.block.hol');
  check('no block keyword is scoped differently from the rest',
        odd.length === 0, odd);
}

console.log(failed === 0 ? '\nall checks passed' : '\n' + failed + ' check(s) failed');
process.exit(failed === 0 ? 0 : 1);
