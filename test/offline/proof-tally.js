// The proof tally, checked without VS Code.
//
// `npm test` drives a real extension host through @vscode/test-electron,
// which needs to download one; this needs nothing but node.  It stubs
// the `vscode` module, patches LanguageClient.start to record rather
// than spawn, and drives the real compiled out/lspClient.js.
//
// What it guards: the tally is keyed by proof *name*.  Keyed by name
// and line, as it once was, a proof that an edit moved was announced
// under two identities and counted twice -- "61 proofs checked" became
// 62, then 68, and adding a line at the top of a 61-theorem file gave
// 122 entries.  Run with `npm run test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

// `test:offline' chains these files with `&&', so one that never
// returns stalls the suite with nothing said.  Fail instead: this
// file once hung outright, on a prompt loop whose stub never let go.
//
// Not `unref'd: an unref'd timer does not hold the process up, so a
// test left waiting on a promise that never settles would run out of
// work and exit 0 -- a hang reported as a pass.  Holding the process
// up costs nothing here, the run ending at the `process.exit' below.
//
// This catches waiting, not spinning.  A loop awaiting already-
// resolved promises -- which is what `readSelectors' does when every
// prompt is answered -- starves the timer queue and no watchdog in
// this process will run.  What rules that out is the input stub
// below, which runs out of answers.
setTimeout(() => {
  console.error('\nproof-tally: timed out -- something never returned');
  process.exit(1);
}, 30000);

let statusText = null;
const listeners = {};
function evt(name) {
  return (fn) => { (listeners[name] = listeners[name] || []).push(fn);
                   return { dispose() {} }; };
}
class EventEmitter {
  constructor() { this.handlers = []; this.event = (fn) => { this.handlers.push(fn); return {dispose(){}}; }; }
  fire(x) { for (const h of this.handlers) h(x); }
  dispose() {}
}
const infoMessages = [];
const vscodeStub = {
  StatusBarAlignment: { Left: 1, Right: 2 },
  ViewColumn: { Beside: -2 },
  EventEmitter,
  Uri: { file: (p) => ({ scheme: 'file', fsPath: p, toString: () => 'file://' + p }) },
  window: {
    activeTextEditor: undefined,
    visibleTextEditors: [],
    createStatusBarItem: () => ({
      show() {}, hide() {}, dispose() {},
      set text(t) { statusText = t; }, get text() { return statusText; },
      tooltip: '', command: '',
    }),
    createOutputChannel: () => ({ appendLine() {}, show() {}, dispose() {} }),
    showInformationMessage: (m) => { infoMessages.push(m); },
    showErrorMessage: (m) => { infoMessages.push(m); },
    createWebviewPanel: () => ({
      webview: { set html(_) {}, },
      onDidDispose: evt('panelDispose'), dispose() {},
    }),
    onDidChangeVisibleTextEditors: evt('visible'),
    onDidChangeActiveTextEditor: evt('active'),
    onDidChangeTextEditorSelection: evt('selection'),
  },
  workspace: {
    getConfiguration: () => ({ get: () => undefined }),
    asRelativePath: (u) => String(u.fsPath || u),
    onDidCloseTextDocument: evt('close'),
    textDocuments: [],
  },
  languages: { createDiagnosticCollection: () => ({ set() {}, dispose() {} }) },
  commands: { registerCommand: () => ({ dispose() {} }) },
};

// The client registers a pile of built-in features, each subscribing to
// `onDid…` hooks we don't model.  Hand out a no-op registrar for any of
// them rather than enumerating them.
function lenient(obj) {
  return new Proxy(obj, {
    get(target, prop) {
      if (prop in target) return target[prop];
      if (typeof prop === 'string' && /^onDid|^onWill/.test(prop)) {
        return () => ({ dispose() {} });
      }
      if (typeof prop === 'string' && /^[A-Z]/.test(prop)) return class {};
      return undefined;
    },
    has() { return true; },
  });
}
vscodeStub.window = lenient(vscodeStub.window);
vscodeStub.workspace = lenient(vscodeStub.workspace);
vscodeStub.languages = lenient(vscodeStub.languages);
vscodeStub.version = '1.90.0';

// vscode-languageclient subclasses API classes it expects the real
// module to export (CompletionItem, CodeAction, …).  Hand out an empty
// class for anything unmodelled rather than enumerating them.
const vscodeProxy = new Proxy(vscodeStub, {
  get(target, prop) {
    if (prop in target) return target[prop];
    if (typeof prop === 'string' && /^[A-Z]/.test(prop)) {
      const cls = class {};
      target[prop] = cls;
      return cls;
    }
    return undefined;
  },
  has() { return true; },
});

const origResolve = Module._resolveFilename;
Module._resolveFilename = function (request, ...rest) {
  if (request === 'vscode') return 'vscode';
  return origResolve.call(this, request, ...rest);
};
require.cache['vscode'] = { id: 'vscode', filename: 'vscode', loaded: true, exports: vscodeProxy };

// Record start() instead of spawning bin/hol, and report Running.
const lcNode = require(path.join(REPO, 'node_modules/vscode-languageclient/node'));
const notified = [];
lcNode.LanguageClient.prototype.start = async function () { this._fakeRunning = true; };
Object.defineProperty(lcNode.LanguageClient.prototype, 'state', {
  get() { return this._fakeRunning ? 2 : 1; },   // State.Running = 2
  configurable: true,
});
lcNode.LanguageClient.prototype.sendNotification = async function (m, p) {
  notified.push([m, p]);
};

const { LspClients, isHolScript } = require(path.join(REPO, 'out/lspClient.js'));

const doc = { uri: vscodeStub.Uri.file('/tmp/fooScript.sml'), languageId: 'hol4' };
let failed = 0;
function check(label, cond, got) {
  console.log((cond ? '  PASS  ' : '  FAIL  ') + label +
              (cond ? '' : '   got: ' + JSON.stringify(got)));
  if (!cond) failed++;
}

// `bin/hol` has to exist for a client to be created; nothing is
// spawned, since `start` is patched above.
const os = require('os');
const fs = require('fs');
const fakeHol = fs.mkdtempSync(path.join(os.tmpdir(), 'holstub-'));
fs.mkdirSync(path.join(fakeHol, 'bin'));
fs.writeFileSync(path.join(fakeHol, 'bin', 'hol'), '', { mode: 0o755 });
const clients = new LspClients(fakeHol);
vscodeStub.window.visibleTextEditors = [{ document: doc }];
vscodeStub.window.activeTextEditor = {
  document: doc, selection: { active: { line: 1, character: 0 } } };
clients.start();
const entry = clients.clients.get(doc.uri.toString());
const handlers = entry.client._pendingNotificationHandlers
                 || entry.client._notificationHandlers;
const send = (states) =>
  handlers.get('$/proofStates')({ uri: doc.uri.toString(), states });
const st = (name, status, line) => ({ name, status, pos: { line } });

// Two proofs settle.
send([st('one', 'proved', 3), st('two', 'proved', 9)]);
check('two proofs read as two', /2 proofs checked/.test(String(statusText)),
      statusText);

// An edit at the top: both are dropped and re-announced one line down.
send([st('one', 'cheated', 4), st('two', 'cheated', 10)]);
check('both outstanding while the pool has let go',
      /proofs 0\/2 \(2 not checked\)/.test(String(statusText)), statusText);
send([st('one', 'proved', 4), st('two', 'checking', 10)]);
check('still two, not four', /proofs 1\/2/.test(String(statusText)),
      statusText);
send([st('two', 'proved', 10)]);
check('and back to two checked', /2 proofs checked/.test(String(statusText)),
      statusText);

// The line follows the proof, so navigation goes to the right place.
send([st('two', 'failed', 10)]);
const out = clients.outstandingProofs();
check('the outstanding proof is reported at the line it moved to',
      out.length === 1 && out[0].name === 'two' && out[0].line === 10, out);

// A rebound name is two proofs, not one: `two' is failed at this
// point, so four entries with two proved and one to look at.
send([st('foo', 'proved', 20), st('foo#2', 'checking', 30)]);
check('a rebound name counts twice, not once',
      /proofs 2\/4 \(1 to look at\)/.test(String(statusText)), statusText);
check('and both occurrences are reachable',
      clients.outstandingProofs().map((p) => p.name).join(',')
        === 'two,foo#2',
      clients.outstandingProofs());

// An unnamed proof is not the user's and is not counted.
send([st('', 'proved', 40)]);
check('an unnamed proof is not counted',
      /proofs 2\/4 \(1 to look at\)/.test(String(statusText)), statusText);

// A proof finished off with suspensions is settled, not outstanding.
// `suspend' splits a long proof into labelled subgoals that `Resume'
// blocks discharge; the parent's own tactic ran and did what it said.
// The tally used to decide by exclusion -- anything not proved,
// checking or cheated was a bad verdict -- so a complete file read
// `proofs 2/3 (1 to look at)'.
//
// `two' is still failed here, which is the control: the count has to
// stay at one, not drop to zero, or this would pass just as well with
// the bad-verdict count broken outright.
send([st('split', 'suspended', 50), st('split[p]', 'proved', 52),
      st('split[q]', 'proved', 55)]);
check('a suspension is not something to look at',
      /proofs 5\/7 \(1 to look at\)/.test(String(statusText)), statusText);
check('and is not listed among the outstanding proofs',
      clients.outstandingProofs().map((p) => p.name).join(',')
        === 'two,foo#2',
      clients.outstandingProofs());

// With the genuinely outstanding two settled, the file is done --
// including the suspended parent, which is counted as checked.
send([st('two', 'proved', 10), st('foo#2', 'proved', 30)]);
check('a file finished off with suspensions reads as checked',
      /7 proofs checked/.test(String(statusText)), statusText);
check('with nothing left to go to',
      clients.outstandingProofs().length === 0,
      clients.outstandingProofs());

// ---- a deleted theorem leaves the tally ---------------------------
// Write a failing proof and it is flagged; delete the whole
// `Theorem ... QED' and it must stop being flagged.  The pool cannot
// say which happened -- it announces a dropped entry as `cheated'
// whether an edit merely reached the proof or the declaration is
// gone -- so the server sends a census on `$/compileCompleted': what
// the buffer still declares, under the names a proof there would be
// given.  Anything it does not name has been deleted or renamed.
//
// Without it the entry stayed for the life of the session: the count
// was wrong, the name was listed in the tooltip, and jumping to it
// landed on whatever now occupies that line.
const completed = (params) =>
  handlers.get('$/compileCompleted')(
    Object.assign({ uri: doc.uri.toString() }, params));
vscodeStub.workspace.textDocuments =
  [{ uri: doc.uri, version: 7, lineCount: 200 }];
const live = ['one', 'foo', 'foo#2', 'split', 'split[p]', 'split[q]'];

send([st('two', 'failed', 10)]);
check('a failing proof is something to look at',
      /proofs 6\/7 \(1 to look at\)/.test(String(statusText)), statusText);

// No census at all -- the server is not checking proofs, or predates
// the field.  That is not the same as a buffer that declares nothing,
// and reading it that way would empty the tally on every compile.
completed({});
check('no census leaves the tally alone',
      /proofs 6\/7 \(1 to look at\)/.test(String(statusText)), statusText);

// A census read from text we have since edited is skipped: the pass
// that edit starts will send one that does apply.
completed({ version: 6, declared: [] });
check('a census for older text is ignored',
      /proofs 6\/7 \(1 to look at\)/.test(String(statusText)), statusText);

completed({ version: 7, declared: live });
check('the deleted proof leaves the tally',
      /6 proofs checked/.test(String(statusText)), statusText);
check('and is no longer somewhere to go',
      clients.outstandingProofs().length === 0,
      clients.outstandingProofs());

// ---- theorem search ----------------------------------------------
// The quick pick is what makes a search usable: it gets the hits as
// items, and picking one opens where the theorem was proved.
let quickPickItems = null;
let opened = null;
// `searchTheorems' reads selectors until one comes back empty, so a
// stub answering the same thing every time never lets it go.  Each
// case scripts the boxes it wants; an exhausted queue yields
// `undefined', which is Escape, so a prompt nobody planned for
// abandons the search rather than spinning.
let boxes = [];
vscodeStub.window.showInputBox = async () => boxes.shift();
vscodeStub.window.showQuickPick = async (items) => {
  quickPickItems = items;
  return items[0];
};
vscodeStub.workspace.openTextDocument = async (u) => { opened = u; return {}; };
vscodeStub.window.showTextDocument = async () => ({
  selection: null, revealRange() {},
});
vscodeStub.Position = class {
  constructor(l, c) { this.line = l; this.character = c; }
};
vscodeStub.Selection = class {};
vscodeStub.Range = class {};
vscodeStub.TextEditorRevealType = { InCenterIfOutsideViewport: 2 };
vscodeStub.Uri.parse = (u) => ({ scheme: 'file', toString: () => u });

const hits = [
  { name: 'ADD_ASSOC', theory: 'arithmetic', class: 'Thm',
    statement: '\u22a2 !m n p.\n  m + (n + p) = m + n + p',
    uri: 'file:///tmp/arithmeticScript.sml', line: 312 },
  { name: 'NOWHERE', theory: 'local', class: 'Def',
    statement: '\u22a2 T', line: 0 },
];
let asked = null;
clients.sendRequest = async (_doc, method, params) => {
  asked = { method, params };
  return hits;
};

const sels = () => asked && JSON.stringify(asked.params.selectors);

(async () => {
  boxes = ['"ASSOC"', "'arithmetic'", ''];
  await clients.searchTheorems();
  check('search asks the server', asked && asked.method === '$/hol/search',
        asked);
  // Sent apart, not joined into one box: the server takes every
  // unquoted run of a single `query' together, having no way to tell
  // where one term pattern ends and the next begins, so one box
  // carries only one pattern.
  check('the selectors go apart, as the user gave them',
        sels() === JSON.stringify(['"ASSOC"', "'arithmetic'"]) &&
        asked.params.limit === 200, asked);
  check('every hit is offered',
        quickPickItems && quickPickItems.length === hits.length,
        quickPickItems);
  check('labelled theory$name, with its class and where it was proved',
        quickPickItems &&
        quickPickItems[0].label === 'arithmetic$ADD_ASSOC' &&
        quickPickItems[0].description === 'Thm  arithmeticScript.sml:312',
        quickPickItems);
  // The fixture's second hit has no location, which HOL does not
  // always record; it must show the class alone rather than a stray
  // separator.
  check('a hit with no location shows just its class',
        quickPickItems && quickPickItems[1].description === 'Def',
        quickPickItems);
  check('and its statement flattened to one line',
        quickPickItems &&
        quickPickItems[0].detail === '\u22a2 !m n p. m + (n + p) = m + n + p',
        quickPickItems && quickPickItems[0].detail);
  check('picking one opens where it was proved',
        opened && String(opened) === 'file:///tmp/arithmeticScript.sml',
        opened);

  // ---- the two ways the selector loop ends ------------------------
  // An empty box runs the search; Escape abandons it.  There is no
  // other exit, so a stub that always answers leaves the loop
  // unbounded -- which is how this file came to hang.
  asked = null; quickPickItems = null;
  boxes = ['"ASSOC"', ''];
  await clients.searchTheorems();
  check('an empty box searches for what came before it',
        sels() === JSON.stringify(['"ASSOC"']), asked);

  asked = null; quickPickItems = null;
  boxes = ['"ASSOC"', undefined];
  await clients.searchTheorems();
  check('Escape abandons the search, asking nothing',
        asked === null && quickPickItems === null,
        { asked, quickPickItems });

  console.log(failed === 0 ? '\nall checks passed'
                           : `\n${failed} check(s) failed`);
  fs.rmSync(fakeHol, { recursive: true, force: true });
  process.exit(failed === 0 ? 0 : 1);
})();
