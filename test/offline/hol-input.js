// Typing HOL connectives, checked without VS Code.
//
// The input method rewrites what you type as you type it, which makes
// it the one feature where being almost right is worse than being
// absent: a rule that fires in the wrong place silently edits your
// source.  So the checks here come in two halves -- that each rule
// produces what `hol-input.el` says it produces, and that none of them
// fire anywhere outside a HOL term.
//
// `holInput.ts` and `holContext.ts` import no `vscode`, so unlike the
// other files here this one needs no module stub at all; it requires
// the real compiled output directly.  Run via `npm run test:offline`.
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

const { BUILTIN_RULES, compileRules, InputMachine, smartQuote } =
  require(path.join(REPO, 'out', 'holInput.js'));
const { classifyOffset } = require(path.join(REPO, 'out', 'holContext.js'));

let failed = 0;
function check(what, ok, got) {
  if (ok) { console.log('  ok   ' + what); }
  else { failed++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
}
function eq(what, got, want) { check(what, got === want, got); }

// Drive the real machine over a plain string buffer, one character at a
// time, the way an editor would.
function type(keys, classify = () => 'term', rules = compileRules()) {
  let buf = '';
  const m = new InputMachine(rules, (o) => classify(buf, o));
  let cursor = 0;
  for (const ch of keys) {
    buf = buf.slice(0, cursor) + ch + buf.slice(cursor);
    cursor += 1;
    const step = m.insert(cursor - 1, ch);
    if (step.edit) {
      const { offset, length, newText } = step.edit;
      buf = buf.slice(0, offset) + newText + buf.slice(offset + length);
      cursor = offset + newText.length;
    }
  }
  return buf;
}

console.log('the eleven rules from hol-input.el');
eq('/\\ is conjunction', type('/\\'), '∧');
eq('\\/ is disjunction', type('\\/'), '∨');
eq('==> is implication', type('==>'), '⇒');
eq('<=> is bi-implication', type('<=>'), '⇔');
eq('<> is disequality', type('<>'), '≠');
eq('<= needs a following character to settle', type('<= '), '≤ ');
eq('! is the universal quantifier', type('!x. P x'), '∀x. P x');
eq('? is the existential', type('?x. P x'), '∃x. P x');
eq('?! is unique existence', type('?!x'), '∃!x');

console.log('\nthe escape hatches');
eq('!! gives back a literal !', type('!!'), '!');
eq('?? gives back a literal ?', type('??'), '?');
eq('!!! is a literal ! then a quantifier', type('!!!'), '!∀');

console.log('\nprefix rules commit provisionally and retract');
eq('<= becomes <=> when > follows', type('<=>'), '⇔');
eq('a dead end keeps the longest prefix that translated', type('<=='), '≤=');
eq('<<= backs off to the live suffix', type('<<='), '<≤');
eq('record syntax <| is left alone', type('<| fld := v'), '<| fld := v');
eq('== alone is not a rule', type('x==y'), 'x==y');
eq('a lone < is untouched', type('a < b'), 'a < b');

console.log('\nrules fire only in HOL terms');
eq('! in SML stays a dereference', type('!r', () => 'sml'), '!r');
eq('<= in SML stays a comparison', type('a <= b', () => 'sml'), 'a <= b');
eq('/\\ in a string is left alone', type('/\\', () => 'string'), '/\\');
eq('/\\ in an embedded language is left alone', type('/\\', () => 'foreign'), '/\\');

console.log('\nthe leader rewriter is told what we ate');
{
  const m = new InputMachine(compileRules(), () => 'term');
  m.insert(0, '/');
  const s = m.insert(1, '\\');
  check('the \\ of /\\ must not start an abbreviation', s.suppressLeaderStart === true, s);
}
{
  const m = new InputMachine(compileRules(), () => 'term');
  const s = m.insert(0, '\\');
  check('a bare \\ still starts an abbreviation', s.suppressLeaderStart === false && !s.edit, s);
}
{
  const m = new InputMachine(compileRules(), () => 'term');
  m.insert(0, '\\');
  const s = m.insert(1, '/');
  check('the \\ of \\/ is reclaimed from the leader',
        !!s.cancelLeaderOver && s.cancelLeaderOver.offset === 0, s);
}

console.log('\nthe machine is never fed its own output');
{
  // `!!` writes a literal `!`.  Were that `!` read back as a keystroke
  // it would fire `!` -> `∀` and the escape hatch would be unreachable.
  const m = new InputMachine(compileRules(), () => 'term');
  m.insert(0, '!');
  const s = m.insert(1, '!');
  check('!! emits a literal ! and leaves the machine idle',
        s.edit.newText === '!' && s.pending === undefined, s);
}

console.log('\nuser rules are merged, not hardcoded');
{
  const r = compileRules({ 'IN': '∈' });
  eq('an added rule fires', type('IN', () => 'term', r), '∈');
  const dropped = compileRules({ '<=': null });
  eq('a removed rule stops firing', type('<= ', () => 'term', dropped), '<= ');
  const amb = compileRules({ '==': '≡' });
  eq('an added rule creates a new ambiguity', type('==', () => 'term', amb), '≡');
  eq('and the longer rule still wins', type('==>', () => 'term', amb), '⇒');
}

console.log('\nwhere the HOL is');
const SCRIPT = [
  /*  0 */ 'open HolKernel boolLib bossLib;',
  /*  1 */ 'val _ = new_theory "demo";',
  /*  2 */ 'val r = ref 0;',
  /*  3 */ 'Theorem both[simp]:',
  /*  4 */ '  !x. x /\\ T <=> x',
  /*  5 */ 'Proof',
  /*  6 */ '  rw[] >> metis_tac[]',
  /*  7 */ 'QED',
  /*  8 */ 'Definition f_def:',
  /*  9 */ '  f x = x + 1',
  /* 10 */ 'Termination',
  /* 11 */ '  WF_REL_TAC `measure I`',
  /* 12 */ 'End',
  /* 13 */ 'Quote cakeml_prog = cakeml:',
  /* 14 */ '  fun g x = if x <= 0 then ! else x;',
  /* 15 */ 'End',
  /* 16 */ 'Theorem simple = CONJ_COMM;',
  /* 17 */ 'val tac = rw[] >> simp[];',
].join('\n');
// Offset of the n'th line's first character, plus a column.
function at(line, col) {
  const lines = SCRIPT.split('\n');
  let o = 0;
  for (let i = 0; i < line; i++) { o += lines[i].length + 1; }
  return o + col;
}
const ctx = (line, col) => classifyOffset(SCRIPT, at(line, col));

eq('top-level SML', ctx(0, 5), 'sml');
eq('an SML ref declaration', ctx(2, 12), 'sml');
eq('a Theorem statement is a term', ctx(4, 5), 'term');
eq('a Proof body is SML', ctx(6, 5), 'sml');
eq('after QED we are back to SML', ctx(16, 0), 'sml');
eq('a Definition body is a term', ctx(9, 5), 'term');
eq('a Termination clause is SML', ctx(11, 3), 'sml');
eq('a backtick quotation inside Termination is a term', ctx(11, 16), 'term');
eq('Theorem name = expr is SML, not a term', ctx(16, 20), 'sml');
eq('a string literal', ctx(1, 22), 'string');
eq('a Quote block body is foreign', ctx(14, 10), 'foreign');
eq('and so is the ! inside it', ctx(14, 30), 'foreign');
eq('End closes the Quote block', ctx(17, 5), 'sml');

{
  // A tactic argument is a term even though the Proof body around it is
  // not -- this is the common case, and the one that nesting is for.
  const s = 'Proof\n  qexists_tac ‘x /\\ y’ >> rw[]\nQED\n';
  eq('a quotation inside a Proof body is a term', classifyOffset(s, s.indexOf('/\\')), 'term');
  eq('the tactic around it is not', classifyOffset(s, s.indexOf('>> rw')), 'sml');
}
{
  const s = 'Theorem t:\n  ‘^(mk_var "x") /\\ y’\nProof\n';
  eq('an antiquotation drops back to SML', classifyOffset(s, s.indexOf('mk_var')), 'sml');
  eq('and the term resumes after it', classifyOffset(s, s.indexOf('/\\')), 'term');
}
{
  const s = 'Theorem t:\n  (* a comment with /\\ in it *)\n  x\nProof\n';
  eq('a comment inside a term', classifyOffset(s, s.indexOf('a comment')), 'comment');
}
{
  const s = 'Theorem unfinished:\n  !x. P x\n\nval y = !r;\n';
  eq('an unterminated Theorem still reads as a term', classifyOffset(s, s.indexOf('P x')), 'term');
}
{
  const s = 'val s = "a ‘ and /\\\\ inside a string";\n';
  eq('quote characters in a string do not open a term',
     classifyOffset(s, s.indexOf('inside')), 'string');
}
{
  const s = 'val x = ``a /\\ b``;\n';
  eq('a double-backtick quotation is a term', classifyOffset(s, s.indexOf('/\\')), 'term');
  eq('and it closes on two backticks', classifyOffset(s, s.length - 1), 'sml');
}

console.log('\nsmart backticks');
const q = (text, pos, cls = () => 'term') => smartQuote(text, pos, pos, cls);
function press(text, pos, cls = () => 'term') {
  const a = q(text, pos, cls);
  if (a.kind === 'literal') { return [text.slice(0, pos) + '`' + text.slice(pos), pos + 1]; }
  if (a.kind === 'move') { return [text, a.to]; }
  let out = text;
  for (const e of a.edits) {
    out = out.slice(0, e.offset) + e.newText + out.slice(e.offset + e.length);
  }
  return [out, a.cursor];
}
{
  let [t, p] = press('', 0);
  eq('one backtick gives a term quotation', t, '‘’');
  eq('with the cursor inside', p, 1);
  [t, p] = press(t, p);
  eq('a second gives a type quotation', t, '“”');
  eq('cursor still inside', p, 1);
  [t, p] = press(t, p);
  eq('a third cycles back', t, '‘’');
}
{
  const [t, p] = press('‘x /\\ y’', 7);
  eq('on a closing quote with content, step over it', t, '‘x /\\ y’');
  eq('and the cursor lands past it', p, 8);
}
{
  const [t, p] = press('‘x /\\ y’', 0);
  eq('on an opening quote, retype the whole quotation', t, '“x /\\ y”');
  eq('and stay on the delimiter that changed', p, 0);
}
{
  const [t] = press('“x”', 0);
  eq('and back again', t, '‘x’');
}
{
  const [t] = press('‘x', 0);
  eq('an unbalanced quotation is refused', t, '`‘x');
}
{
  const a = smartQuote('xy', 0, 2, () => 'term');
  let out = 'xy';
  for (const e of a.edits) {
    out = out.slice(0, e.offset) + e.newText + out.slice(e.offset + e.length);
  }
  eq('a selection is wrapped', out, '‘xy’');
}
{
  const [t] = press('', 0, () => 'string');
  eq('inside a string a backtick stays a backtick', t, '`');
}
{
  const [t] = press('', 0, () => 'foreign');
  eq('and inside an embedded language too', t, '`');
}

console.log(failed === 0 ? '\nall checks passed' : '\n' + failed + ' check(s) failed');
process.exit(failed === 0 ? 0 : 1);
