// Evaluating a selection, and evaluating something typed into a box,
// checked without VS Code.
//
// `npm test` drives a real extension host through @vscode/test-electron,
// which needs to download one; this needs nothing but node.  It stubs
// the `vscode` module, patches LanguageClient.start/sendRequest to
// record rather than spawn, and drives the real compiled
// out/lspClient.js.
//
// What it guards: `Ctrl+H Ctrl+E` with nothing selected used to send
// the blank-line-delimited block around the cursor, so getting a value
// out of the session meant typing the expression into the script and
// deleting it again.  It now prompts, and the prompt carries the
// session's history.  The checks pin which of the two paths runs, what
// reaches `$/eval`, and that Escape sends nothing -- a prompt whose
// cancellation still evaluated would run whatever was left in the box.
// Run with `npm run test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

// `test:offline' chains these files with `&&', so one that never
// returns stalls the suite with nothing said.  Fail instead.  Not
// `unref'd: an unref'd timer does not hold the process up, so a test
// left waiting on a promise that never settles would run out of work
// and exit 0 -- a hang reported as a pass.
setTimeout(() => {
  console.error('\neval-prompt: timed out -- something never returned');
  process.exit(1);
}, 30000);

const listeners = {};
function evt(name) {
  return (fn) => { (listeners[name] = listeners[name] || []).push(fn);
                   return { dispose() {} }; };
}
class EventEmitter {
  constructor() {
    this.handlers = [];
    this.event = (fn) => { this.handlers.push(fn); return { dispose() {} }; };
  }
  fire(x) { for (const h of this.handlers) h(x); }
  dispose() {}
}

const infoMessages = [];
const channelLines = [];
const vscodeStub = {
  StatusBarAlignment: { Left: 1, Right: 2 },
  ViewColumn: { Beside: -2 },
  EventEmitter,
  Uri: { file: (p) => ({ scheme: 'file', fsPath: p,
                         toString: () => 'file://' + p }) },
  window: {
    activeTextEditor: undefined,
    visibleTextEditors: [],
    createStatusBarItem: () => ({
      show() {}, hide() {}, dispose() {}, text: '', tooltip: '', command: '',
    }),
    createOutputChannel: () => ({
      appendLine(l) { channelLines.push(l); }, show() {}, dispose() {},
    }),
    showInformationMessage: (m) => { infoMessages.push(m); },
    showErrorMessage: (m) => { infoMessages.push(m); },
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

// ---- the quick pick ------------------------------------------------
// What the next prompt does, set by each case below.  `null' is
// Escape: VS Code hides the box without accepting, which has to reach
// the caller as "abandoned" and not as an empty expression.
let nextAnswer = null;
let prompts = 0;
// Every assignment to `items', in order, for the prompt now open: the
// first is the history as the box opened with it, the rest are what
// typing narrowed it to.
let itemsLog = [];

vscodeStub.window.createQuickPick = () => {
  const box = {
    title: '', placeholder: '', value: '', ignoreFocusOut: false,
    selectedItems: [], _items: [],
    get items() { return this._items; },
    set items(v) { this._items = v; itemsLog.push(v.map((i) => i.label)); },
    onDidChangeValue(fn) { this._onValue = fn; return { dispose() {} }; },
    onDidAccept(fn) { this._onAccept = fn; return { dispose() {} }; },
    onDidHide(fn) { this._onHide = fn; return { dispose() {} }; },
    show() {
      prompts++;
      // The handlers are all registered by the time `show' is called,
      // so the interaction can be driven from here.
      if (nextAnswer === null) { this._onHide(); return; }
      this.value = nextAnswer.type;
      this._onValue(this.value);
      if (nextAnswer.pick !== undefined) {
        this.selectedItems = [this._items[nextAnswer.pick]];
      }
      this._onAccept();
    },
    // `dispose' fires `onDidHide' in VS Code too; the promise must
    // already be settled by then or an accepted expression would be
    // overwritten by the Escape answer.
    dispose() { if (this._onHide) this._onHide(); },
  };
  return box;
};

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
require.cache['vscode'] = {
  id: 'vscode', filename: 'vscode', loaded: true, exports: vscodeProxy,
};

// Record start()/sendRequest() instead of spawning bin/hol.
const lcNode = require(path.join(REPO,
                                 'node_modules/vscode-languageclient/node'));
lcNode.LanguageClient.prototype.start = async function () {
  this._fakeRunning = true;
};
Object.defineProperty(lcNode.LanguageClient.prototype, 'state', {
  get() { return this._fakeRunning ? 2 : 1; },   // State.Running = 2
  configurable: true,
});
lcNode.LanguageClient.prototype.sendNotification = async function () {};
const requests = [];
lcNode.LanguageClient.prototype.sendRequest = async function (m, p) {
  requests.push({ method: m, params: p });
  return null;
};

const { LspClients } = require(path.join(REPO, 'out/lspClient.js'));

let failed = 0;
function check(label, cond, got) {
  console.log((cond ? '  PASS  ' : '  FAIL  ') + label +
              (cond ? '' : '   got: ' + JSON.stringify(got)));
  if (!cond) failed++;
}

const SELECTED = 'listTheory.APPEND';
const doc = {
  uri: vscodeStub.Uri.file('/tmp/fooScript.sml'),
  languageId: 'hol4',
  getText: () => SELECTED,
};
const withSelection = {
  document: doc,
  selection: { isEmpty: false, start: { line: 4, character: 2 },
               active: { line: 4, character: 19 } },
};
const noSelection = {
  document: doc,
  selection: { isEmpty: true, start: { line: 6, character: 0 },
               active: { line: 6, character: 0 } },
};

const os = require('os');
const fs = require('fs');
const fakeHol = fs.mkdtempSync(path.join(os.tmpdir(), 'holstub-'));
fs.mkdirSync(path.join(fakeHol, 'bin'));
fs.writeFileSync(path.join(fakeHol, 'bin', 'hol'), '', { mode: 0o755 });
const clients = new LspClients(fakeHol);
vscodeStub.window.visibleTextEditors = [{ document: doc }];
vscodeStub.window.activeTextEditor = noSelection;
clients.start();

const lastEval = () => requests.filter((r) => r.method === '$/eval').pop();
function prompt(answer) { nextAnswer = answer; itemsLog = []; }

(async () => {
  // ---- a selection is still a selection ----------------------------
  prompts = 0;
  await clients.evalSelection(withSelection);
  check('a selection goes straight to the server',
        lastEval() && lastEval().params.code === SELECTED, lastEval());
  check('at where the selection starts',
        lastEval() && lastEval().params.position.line === 4 &&
        lastEval().params.position.character === 2, lastEval());
  check('and opens no box', prompts === 0, prompts);

  // ---- nothing selected: the box ----------------------------------
  // The old fallback sent the blank-line-delimited block around the
  // cursor, which is why an expression had to be typed into the
  // script to be evaluated at all.
  prompt({ type: '3 * 13' });
  await clients.evalSelection(noSelection);
  check('with nothing selected the box opens', prompts === 1, prompts);
  check('and what was typed is what is evaluated',
        lastEval() && lastEval().params.code === '3 * 13', lastEval());
  check('at the cursor, not at the end of the file',
        lastEval() && lastEval().params.position.line === 6 &&
        lastEval().params.position.character === 0, lastEval());
  check('the transcript echoes it',
        channelLines.includes('> 3 * 13'), channelLines);

  // ---- the history ------------------------------------------------
  prompt({ type: 'DB.match [] (Term`$+`)' });
  await clients.evalPrompt(noSelection);
  check('the box opens on what has been asked before',
        JSON.stringify(itemsLog[0]) === JSON.stringify(['3 * 13']), itemsLog);
  check('and what is typed heads the list, so Enter takes it',
        JSON.stringify(itemsLog[1]) ===
          JSON.stringify(['DB.match [] (Term`$+`)', '3 * 13']), itemsLog);

  // Newest first, and picking an old one moves it back up rather than
  // listing it twice -- a history that grew a duplicate per repeat
  // would bury everything else within a session.
  prompt({ type: '', pick: 1 });
  await clients.evalPrompt(noSelection);
  check('newest first',
        JSON.stringify(itemsLog[0]) ===
          JSON.stringify(['DB.match [] (Term`$+`)', '3 * 13']), itemsLog);
  check('picking an old one evaluates it',
        lastEval() && lastEval().params.code === '3 * 13', lastEval());

  prompt({ type: 'x' });
  await clients.evalPrompt(noSelection);
  check('and moves it up rather than duplicating it',
        JSON.stringify(itemsLog[0]) ===
          JSON.stringify(['3 * 13', 'DB.match [] (Term`$+`)']), itemsLog);

  // ---- Escape ------------------------------------------------------
  const before = requests.length;
  prompt(null);
  await clients.evalPrompt(noSelection);
  check('Escape evaluates nothing',
        requests.length === before, requests.slice(before));

  // An empty box is not an expression either.  It cannot be told from
  // Escape by its text, only by which callback fired, so both exits
  // are checked.
  prompt({ type: '   ' });
  await clients.evalPrompt(noSelection);
  check('nor does a blank one', requests.length === before,
        requests.slice(before));

  console.log(failed === 0 ? '\nall checks passed'
                           : `\n${failed} check(s) failed`);
  fs.rmSync(fakeHol, { recursive: true, force: true });
  process.exit(failed === 0 ? 0 : 1);
})();
