// How the language client is wired up, checked without VS Code.
//
// vscode-languageclient resolves the trace setting through
// `workspace.getConfiguration(<client id>)`, so the client's id *is*
// the settings section.  An id carrying the script's path -- which is
// what this client used to pass -- cannot be named in settings.json,
// so `trace.server` was unreachable and no transcript could be
// captured.  These checks pin the id, the channel, and the handoff.
//
// The real vscode-languageclient is exercised: `vscode` is stubbed and
// `LanguageClient.start` is patched so nothing spawns a heap.  Run via
// `npm run test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

const asked = [];
const channels = [];
const panels = [];
const stub = new Proxy({
  Uri: { file: (p) => ({ scheme: 'file', fsPath: p, toString: () => 'file://' + p }) },
  ViewColumn: { Beside: -2 },
  StatusBarAlignment: { Left: 1, Right: 2 },
  ThemeColor: class { constructor(id){ this.id = id; } },
  version: '1.90.0',
  window: {
    createOutputChannel: (name) => { channels.push(name);
      return { name, appendLine(){}, append(){}, show(){}, dispose(){} }; },
    showErrorMessage: () => Promise.resolve(),
    createStatusBarItem: () => ({ text: '', tooltip: '', command: undefined,
      backgroundColor: undefined, show(){}, hide(){}, dispose(){} }),
    createWebviewPanel: (_id, _title, _col, _opts) => {
      const panel = {
        written: [],
        webview: {
          set html(v) { panel.written.push(v); },
          get html() { return panel.written[panel.written.length - 1]; },
          onDidReceiveMessage: () => ({ dispose(){} }),
        },
        onDidDispose: (fn) => { panel.disposeHandler = fn;
                                return { dispose(){} }; },
        reveal(){},
        dispose(){ if (panel.disposeHandler) panel.disposeHandler(); },
      };
      panels.push(panel);
      return panel;
    },
    onDidChangeActiveTextEditor: () => ({ dispose(){} }),
    onDidChangeVisibleTextEditors: () => ({ dispose(){} }),
    visibleTextEditors: [],
  },
  workspace: {
    getConfiguration: (section) => { asked.push(section);
      return { get: (k, d) => (section === 'hol4-lsp' && k === 'trace.server')
                 ? 'verbose' : d }; },
    asRelativePath: (u) => String(u.fsPath || u),
    onDidChangeConfiguration: () => ({ dispose(){} }),
    onDidCloseTextDocument: () => ({ dispose(){} }),
    onDidOpenTextDocument: () => ({ dispose(){} }),
    textDocuments: [],
  },
  languages: { createDiagnosticCollection: () => ({ dispose(){} }) },
  commands: { registerCommand: () => ({ dispose(){} }) },
  // A real one: the tests below observe what the extension fires, so
  // an emitter that swallows `fire` would pass them regardless.
  EventEmitter: class {
    constructor() {
      this.listeners = [];
      this.event = (fn) => {
        this.listeners.push(fn);
        return { dispose: () => {
          this.listeners = this.listeners.filter((l) => l !== fn); } };
      };
    }
    fire(v) { for (const l of [...this.listeners]) l(v); }
    dispose() { this.listeners = []; }
  },
}, { get(t, k) { if (k in t) return t[k];
      return class Anon { constructor(){} static from(){ return new Anon(); } }; } });

// Any `onDid…` the client's built-in features hook must answer with a
// disposable; enumerating them by hand is a losing game.
const lenient = (base) => new Proxy(base, {
  get(t, k) {
    if (k in t) return t[k];
    if (typeof k === 'string' && k.startsWith('onDid'))
      return () => ({ dispose() {} });
    return undefined;
  },
});
stub.workspace = lenient(stub.workspace);
stub.window = lenient(stub.window);
stub.languages = lenient(stub.languages);

const oR = Module._resolveFilename;
Module._resolveFilename = function (r, ...a) {
  return r === 'vscode' ? 'vscode' : oR.call(this, r, ...a); };
const oL = Module._load;
Module._load = function (r, ...a) {
  return r === 'vscode' ? stub : oL.call(this, r, ...a); };

const lc = require(path.join(REPO, 'node_modules/vscode-languageclient/node'));
const built = [];
const RealLC = lc.LanguageClient;
const notified = new Map();
class FakeLC extends RealLC {
  constructor(id, name, so, co) { super(id, name, so, co); built.push({ id, name, co }); }
  start() { return Promise.resolve(); }
  stop() { return Promise.resolve(); }
  get state() { return 2; }
  // Record rather than register: with no connection there is nothing to
  // deliver a notification, and what these tests check is what the
  // extension does when one arrives.
  onNotification(method, handler) {
    notified.set(method, handler);
    return { dispose() {} };
  }
}
lc.LanguageClient = FakeLC;

const { LspClients, TRACE_SECTION } = require(path.join(REPO, 'out/lspClient.js'));

let fail = 0;
const ok = (what, cond, got) => {
  if (cond) console.log('  ok   ' + what);
  else { fail++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
};

console.log('lsp trace wiring');
ok('the section is the plain `hol4-lsp`, nameable in settings.json',
   TRACE_SECTION === 'hol4-lsp', TRACE_SECTION);

const cs = new LspClients('/nonexistent-holdir');
const doc = { uri: stub.Uri.file('/tmp/fooScript.sml'), fsPath: '/tmp/fooScript.sml' };
const entry = cs.create('/bin/true', doc);

ok('the client id is the section, not the file path',
   built.length === 1 && built[0].id === 'hol4-lsp', built.map(b => b.id));
ok('the display name still names the file',
   /fooScript\.sml/.test(built[0].name), built[0].name);
ok('a trace channel is created beside the output one',
   channels.some(c => /^HOL4 LSP Trace: /.test(c)) &&
     channels.some(c => /^HOL4 LSP: /.test(c)), channels);
ok('and it is handed to the client as traceOutputChannel',
   built[0].co.traceOutputChannel !== undefined &&
     /Trace/.test(built[0].co.traceOutputChannel.name),
   built[0].co.traceOutputChannel && built[0].co.traceOutputChannel.name);

// The real client resolves trace through getConfiguration(this._id).
const resolved = entry.client.getConfiguration
  ? undefined : stub.workspace.getConfiguration('hol4-lsp').get('trace.server', 'off');
ok('the section the client would consult yields our setting',
   resolved === 'verbose', resolved);
ok('and the entry carries the channel so disposal can reach it',
   entry.trace !== undefined, Object.keys(entry));

// --- the goals pane hears about a finished compile ----------------
// Until the compile lands the server has no state to walk and answers
// nothing, so the pane has to be told when that changes.  The signal
// used to be a side effect of clearing the dependency block, which says
// nothing when there was no block to clear -- the ordinary case -- and
// left the pane empty until the user moved the cursor.
console.log('\ncompile-completed refresh');
let fired = 0;
cs.onDidChangeClientState(() => { fired++; });
const completed = notified.get('$/compileCompleted');
ok('the client subscribes to $/compileCompleted',
   typeof completed === 'function', typeof completed);
if (typeof completed === 'function') {
  completed({ uri: doc.uri.toString() });
  ok('and a completed compile tells the pane to re-ask', fired === 1, fired);
}

// --- the goals pane, scrolled to its end and left alone ------------
// The active goal comes last and ends with its conclusion, so the end
// of the page is the part worth showing.  Assigning `webview.html'
// reloads the document, which scrolls it back to the top -- so an
// auto-follow tick that renders the same state must not assign at all,
// or it would yank a state the user is reading back to the top.
console.log('\ngoals pane');
const { GoalsView } = require(path.join(REPO, 'out/goalsView.js'));
const gv = new GoalsView(cs);
gv.show();
const panel = panels[panels.length - 1];
const page = panel.written[0];
ok('the page knows how to reach its end',
   /scroller\.scrollTop = scroller\.scrollHeight/.test(page), true);
// The head must sit outside the element that scrolls, or scrolling to
// the end takes it out of view -- which is the whole point of it.
ok('and the head is outside the scrolling part',
   page.indexOf('id="head"') < page.indexOf('id="scroll"') &&
     !/id="scroll"[^]*id="head"/.test(page), true);
// Defining it is not doing it: check the call as well as the function.
ok('and does so as it is parsed',
   /^\s*toBottom\(\);\s*$/m.test(page), true);
ok('and again once layout has settled',
   /addEventListener\('load', toBottom\)/.test(page), true);

const before = panel.written.length;
gv.renderIdle('the same thing');
gv.renderIdle('the same thing');
ok('an unchanged render is not written twice',
   panel.written.length === before + 1, panel.written.length - before);
gv.renderIdle('something else');
ok('and a changed one is written',
   panel.written.length === before + 2, panel.written.length - before);

console.log(fail === 0 ? '\nall checks passed' : `\n${fail} check(s) failed`);
process.exit(fail ? 1 : 0);
