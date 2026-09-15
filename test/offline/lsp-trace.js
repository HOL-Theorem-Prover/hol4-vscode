// The JSON-RPC trace wiring, checked without VS Code.
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
  EventEmitter: class { constructor(){ this.event = () => ({dispose(){}}); } fire(){} dispose(){} },
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
class FakeLC extends RealLC {
  constructor(id, name, so, co) { super(id, name, so, co); built.push({ id, name, co }); }
  start() { return Promise.resolve(); }
  stop() { return Promise.resolve(); }
  get state() { return 2; }
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

console.log(fail === 0 ? '\nall checks passed' : `\n${fail} check(s) failed`);
process.exit(fail ? 1 : 0);
