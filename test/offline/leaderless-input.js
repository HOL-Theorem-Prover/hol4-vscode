// The leaderless input method, driven through the real rewriter.
//
// `hol-input.js` checks the state machine in isolation.  This file
// checks the part that machine cannot see: that its rewrites actually
// reach the document, that the `\`-leader rewriter it shares a change
// listener with still works, and above all that it is never fed its own
// output.  That last one is not academic -- `!!` writes a literal `!`,
// and if that `!` came back round as a keystroke it would turn into `∀`
// and a literal `!` would be untypable.
//
// `vscode` is stubbed and the real compiled out/abbreviations.js is
// driven.  Run via `npm run test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

class Pos { constructor(o) { this.o = o; } translate() { return this; } }
class Rng {
  constructor(start, end) { this.start = start; this.end = end; }
}
class Sel extends Rng { }

let settings = {};
const vscodeStub = {
  Range: Rng, Position: Pos, Selection: Sel, Hover: class { },
  window: {
    activeTextEditor: undefined,
    createTextEditorDecorationType: () => ({ dispose() { } }),
    onDidChangeTextEditorSelection: (cb) => { hooks.selection = cb; return { dispose() { } }; },
    onDidChangeActiveTextEditor: () => ({ dispose() { } }),
  },
  workspace: {
    onDidChangeTextDocument: (cb) => { hooks.change = cb; return { dispose() { } }; },
    onDidChangeConfiguration: () => ({ dispose() { } }),
    getConfiguration: () => ({ get: (k, d) => (k in settings ? settings[k] : d) }),
  },
  commands: {
    registerTextEditorCommand: () => ({ dispose() { } }),
    executeCommand: async () => undefined,
  },
  languages: {
    registerHoverProvider: () => ({ dispose() { } }),
    match: () => 1,
  },
  extensions: { getExtension: () => undefined, onDidChange: () => ({ dispose() { } }) },
};
const hooks = {};

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

const { AbbreviationFeature } = require(path.join(REPO, 'out', 'abbreviations.js'));

let failed = 0;
function check(what, ok, got) {
  if (ok) { console.log('  ok   ' + what); }
  else { failed++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
}
function eq(what, got, want) { check(what, got === want, got); }

// A document and an editor, just real enough for the rewriter.
function makeEditor(initial) {
  const doc = {
    text: initial,
    version: 1,
    getText() { return this.text; },
    offsetAt(p) { return p.o; },
    positionAt(o) { return new Pos(o); },
    lineAt() { return { text: '' }; },
  };
  const editor = {
    document: doc,
    selections: [new Sel(new Pos(initial.length), new Pos(initial.length))],
    setDecorations() { },
    async edit(cb) {
      const edits = [];
      cb({ replace: (r, t) => edits.push([r.start.o, r.end.o, t]) });
      // Apply back to front so earlier offsets stay valid.
      edits.sort((a, b) => b[0] - a[0]);
      for (const [s, e, t] of edits) {
        doc.text = doc.text.slice(0, s) + t + doc.text.slice(e);
      }
      return true;
    },
  };
  Object.defineProperty(editor, 'selection', { get() { return this.selections[0]; } });
  return editor;
}

// Type one character the way VS Code would: mutate the document, then
// tell the listener about it.
async function typeInto(editor, keys) {
  const doc = editor.document;
  let cursor = doc.text.length;
  for (const ch of keys) {
    const before = doc.text.length;
    doc.text = doc.text.slice(0, cursor) + ch + doc.text.slice(cursor);
    doc.version++;
    const at = cursor;
    cursor += 1;
    editor.selections = [new Sel(new Pos(cursor), new Pos(cursor))];
    await hooks.change({
      document: doc,
      contentChanges: [{ rangeOffset: at, rangeLength: 0, text: ch }],
    });
    // The rewriter's edit may have changed the length; keep the cursor
    // at the end, which is where typing leaves it.
    cursor += doc.text.length - before - 1;
    editor.selections = [new Sel(new Pos(cursor), new Pos(cursor))];
  }
  return doc.text;
}

async function run(initial, keys, opts = {}) {
  settings = opts;
  const editor = makeEditor(initial);
  vscodeStub.window.activeTextEditor = editor;
  const feature = new AbbreviationFeature();
  const out = await typeInto(editor, keys);
  feature.dispose();
  return out;
}

(async () => {
  console.log('rewrites reach the document');
  eq('/\\ in a quotation', await run('val t = ‘', '/\\'), 'val t = ‘∧');
  eq('==> in a Theorem statement',
     await run('Theorem t:\n  ', 'p ==> q'), 'Theorem t:\n  p ⇒ q');
  eq('! settles once the bound variable arrives',
     await run('Theorem t:\n  ', '!x'), 'Theorem t:\n  ∀x');

  console.log('\nthe escape hatch survives the round trip');
  // The rewriter sees its own edit come back through the listener.  If
  // that is read as a keystroke, this comes out as ∀.
  eq('!! is a literal !', await run('Theorem t:\n  ', '!!'), 'Theorem t:\n  !');
  eq('?? is a literal ?', await run('Theorem t:\n  ', '??'), 'Theorem t:\n  ?');
  eq('?! is unique existence', await run('Theorem t:\n  ', '?!x'), 'Theorem t:\n  ∃!x');

  console.log('\nit stays out of the SML');
  eq('a ref dereference', await run('val r = ref 0;\nval x = ', '!r'),
     'val r = ref 0;\nval x = !r');
  eq('a comparison in a Proof body',
     await run('Proof\n  ', 'if a <= b then'), 'Proof\n  if a <= b then');
  eq('an embedded language is untouched',
     await run('Quote cml = cakeml:\n  ', 'x /\\ y'), 'Quote cml = cakeml:\n  x /\\ y');

  console.log('\nthe leader rewriter still has its backslash');
  eq('\\alpha still resolves', await run('Theorem t:\n  ', '\\alpha '),
     'Theorem t:\n  α ');
  eq('\\/ is disjunction, not an abbreviation',
     await run('Theorem t:\n  p ', '\\/ q'), 'Theorem t:\n  p ∨ q');
  eq('/\\ is conjunction, and eats the leader',
     await run('Theorem t:\n  p ', '/\\ q'), 'Theorem t:\n  p ∧ q');

  console.log('\nthe setting turns it off');
  eq('leaderless off leaves ASCII alone',
     await run('Theorem t:\n  ', 'p ==> q', { 'input.leaderless': false }),
     'Theorem t:\n  p ==> q');
  eq('but the leader still works',
     await run('Theorem t:\n  ', '\\alpha ', { 'input.leaderless': false }),
     'Theorem t:\n  α ');

  console.log('\nuser rules reach the machine');
  eq('an added rule fires',
     await run('Theorem t:\n  x ', 'IN s', { 'input.rules': { IN: '∈' } }),
     'Theorem t:\n  x ∈ s');

  console.log(failed === 0 ? '\nall checks passed' : '\n' + failed + ' check(s) failed');
  process.exit(failed === 0 ? 0 : 1);
})();
