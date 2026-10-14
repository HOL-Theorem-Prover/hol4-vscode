// Running Holmake from the editor, checked without VS Code.
//
// `npm test' drives a real extension host through
// @vscode/test-electron, which needs to download one; this needs
// nothing but node.  It stubs the `vscode' module and drives the real
// compiled out/holmake.js.
//
// What it guards: the command used to open a terminal whose *shell*
// was Holmake (`createTerminal({shellPath: 'Holmake'})').  A terminal
// dies with its root process, so the panel and everything Holmake had
// printed went the instant it exited -- and a failed build, a clean
// one, and a Holmake that was never installed all looked identical.
// The run is now a task, whose terminal VS Code keeps, and whose exit
// code comes back on `onDidEndTaskProcess'.
//
// What this cannot check is that VS Code really keeps that terminal:
// that is the extension host's behaviour, not ours.  What it pins is
// the contract that produces it -- `close' not set, a dedicated
// panel, and no `createTerminal' call to put `shellPath' back.
//
// It guards a second thing since: that a failure leaves you looking
// at that terminal.  The Output view and the Terminal view are one
// slot at the bottom of the window, so reporting the failure through
// `error' -- which reveals the `HOL: Editor' channel -- hid the
// output behind a single line naming the exit code.  The stub's
// `show()' used to do nothing, which is why this file watched that
// happen for a release without noticing.
// Run with `npm run test:offline'.
const Module = require('module');
const path = require('path');
const fs = require('fs');
const os = require('os');
const REPO = path.join(__dirname, '..', '..');

// `test:offline' chains these files with `&&', so one that never
// returns stalls the suite with nothing said.  Fail instead.  Not
// `unref'd: an unref'd timer does not hold the process up, so a test
// left waiting on a promise that never settles would run out of work
// and exit 0 -- a hang reported as a pass.
setTimeout(() => {
  console.error('\nholmake: timed out -- something never returned');
  process.exit(1);
}, 30000);

// ---- recorders -----------------------------------------------------
let executed = [];          // tasks handed to executeTask
let terminals = [];         // createTerminal options (should stay empty)
let errors = [];            // showErrorMessage
let infos = [];             // showInformationMessage
let statuses = [];          // setStatusBarMessage
let channelLines = [];      // the HOL: Editor channel, flattened
let channels = new Map();   // name -> { lines, shows }
let openTerminals = [];     // what `window.terminals' answers
let settings = {};          // hol4-mode.* configuration
let folder = undefined;     // what getWorkspaceFolder answers
let executeThrows = false;

// A channel by name, created on demand, recording both what was
// written to it and every time it was brought to the front.  The
// stub used to return a `show()' that did nothing, which is exactly
// why the bug this file now guards was invisible here.
function channel(name) {
  if (!channels.has(name)) { channels.set(name, { lines: [], shows: [] }); }
  return channels.get(name);
}

function reset() {
  // Retire the previous Holmake first: its event handlers are in the
  // arrays cleared below, and a handler outliving its owner reports
  // the next test's events to the last test's object.
  if (live) { live.dispose(); live = null; }
  executed = []; terminals = []; errors = []; infos = [];
  statuses = []; channelLines = []; channels = new Map();
  openTerminals = []; settings = {};
  folder = undefined; executeThrows = false;
  endHandlers.length = 0; startHandlers.length = 0;
  openHandlers.length = 0; closeHandlers.length = 0;
  reload();
}

// ---- the vscode stub -----------------------------------------------
class Task {
  constructor(definition, scope, name, source, execution) {
    this.definition = definition;
    this.scope = scope;
    this.name = name;
    this.source = source;
    this.execution = execution;
    this.presentationOptions = {};
  }
}
class ProcessExecution {
  constructor(process_, args, options) {
    this.process = process_;
    this.args = args;
    this.options = options;
  }
}

// Every live `onDidEndTaskProcess' handler.  Disposing removes it, so
// a test that builds a second `Holmake' after disposing the first
// does not get every event reported twice.
const endHandlers = [];
function fireEnd(e) {
  for (const h of endHandlers.slice()) { h(e); }
}
const startHandlers = [];
function fireStart(e) {
  for (const h of startHandlers.slice()) { h(e); }
}
const openHandlers = [];
const closeHandlers = [];

// Subscribing, the way every one of these events does it.
function subscribe(list, fn) {
  list.push(fn);
  return { dispose() {
    const i = list.indexOf(fn);
    if (i >= 0) { list.splice(i, 1); }
  } };
}

/** A terminal, with the root-process id the extension identifies it
 * by and a `show' that records its `preserveFocus' argument. */
function fakeTerminal(pid, name) {
  const t = {
    name: name || 'HOL: Holmake (src)',
    processId: Promise.resolve(pid),
    shows: [],
    show(preserveFocus) { t.shows.push(preserveFocus); },
    sendText() {}, dispose() {},
  };
  return t;
}
function openTerminal(t) {
  openTerminals.push(t);
  for (const h of openHandlers.slice()) { h(t); }
  return t;
}
function closeTerminal(t) {
  const i = openTerminals.indexOf(t);
  if (i >= 0) { openTerminals.splice(i, 1); }
  for (const h of closeHandlers.slice()) { h(t); }
}

// Identifying a terminal reads `Terminal.processId', which is a
// promise, so the extension finishes that work a turn or two after
// the event that started it.  Wait for the queue to drain rather
// than for a number of turns that a refactor would invalidate.
function settle() {
  return new Promise((resolve) => setImmediate(resolve));
}

const vscodeStub = {
  Uri: { file: (p) => ({ scheme: 'file', fsPath: p,
                         toString: () => 'file://' + p }) },
  Task,
  ProcessExecution,
  TaskScope: { Global: 1, Workspace: 2 },
  TaskRevealKind: { Always: 1, Silent: 2, Never: 3 },
  TaskPanelKind: { Shared: 1, Dedicated: 2, New: 3 },
  TaskGroup: { Build: { id: 'build' } },
  window: {
    createOutputChannel: (name) => {
      const c = channel(name);
      return {
        name,
        appendLine(l) { c.lines.push(l); channelLines.push(l); },
        show(preserveFocus) { c.shows.push(preserveFocus); },
        dispose() {},
      };
    },
    showErrorMessage: (m) => { errors.push(m); },
    showInformationMessage: (m) => { infos.push(m); },
    setStatusBarMessage: (m) => { statuses.push(m); },
    createTerminal: (opts) => {
      terminals.push(opts);
      return openTerminal(fakeTerminal(undefined, opts && opts.name));
    },
    // A live view, as the real one is: a terminal opened after the
    // extension last looked must still be there when it looks again.
    get terminals() { return openTerminals; },
    onDidOpenTerminal: (fn) => subscribe(openHandlers, fn),
    onDidCloseTerminal: (fn) => subscribe(closeHandlers, fn),
  },
  workspace: {
    getConfiguration: () => ({
      get: (key) => settings[key],
    }),
    getWorkspaceFolder: () => folder,
  },
  tasks: {
    executeTask: async (task) => {
      if (executeThrows) { throw new Error('no process can be started'); }
      const exec = { task, terminate() {} };
      executed.push({ task, exec });
      return exec;
    },
    onDidEndTaskProcess: (fn) => subscribe(endHandlers, fn),
    onDidStartTaskProcess: (fn) => subscribe(startHandlers, fn),
  },
};

const origResolve = Module._resolveFilename;
Module._resolveFilename = function (request, ...rest) {
  if (request === 'vscode') { return 'vscode'; }
  return origResolve.call(this, request, ...rest);
};
require.cache['vscode'] = {
  id: 'vscode', filename: 'vscode', loaded: true, exports: vscodeStub,
};

// `out/common.js' keeps two pieces of module-level state: the
// `HOL: Editor' channel, and a `firstError' latch that lets the very
// first error of a session -- and only that one -- bring the channel
// to the front.  One latch per node process means one for this whole
// file, and the checks above spend it long before the ones below
// run: a reveal assertion written at the bottom of the file would
// see nothing *whether or not the bug were present*, and pass for
// the wrong reason.  So each block starts from freshly loaded
// modules.  Both must go: `out/holmake.js' binds the common module's
// exports object once, so dropping only `out/common.js' leaves it
// talking to the old one.  The `vscode' entry stays -- that is the
// stub, and `require.resolve' never sees it, the hook above
// intercepting only the literal name.
//
// The other offline tests require their module once and never reset
// it; this one is the first that cannot.
let Holmake;
function reload() {
  for (const m of ['out/common.js', 'out/holmake.js']) {
    delete require.cache[require.resolve(path.join(REPO, m))];
  }
  ({ Holmake } = require(path.join(REPO, 'out/holmake.js')));
}
reload();

let failed = 0;
function check(label, cond, got) {
  console.log((cond ? '  PASS  ' : '  FAIL  ') + label +
              (cond ? '' : '   got: ' + JSON.stringify(got)));
  if (!cond) { failed++; }
}

// ---- the world on disk ---------------------------------------------
// A real directory with a real executable in it: resolution stats the
// candidate, so a made-up path would be rejected for the right reason
// by accident and prove nothing.
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'holmake-test-'));
const holdir = path.join(tmp, 'hol');
fs.mkdirSync(path.join(holdir, 'bin'), { recursive: true });
const holmakeBin = path.join(holdir, 'bin', 'Holmake');
fs.writeFileSync(holmakeBin, '#!/bin/sh\nexit 0\n');
fs.chmodSync(holmakeBin, 0o755);

// A second one, reachable only through the PATH.
const pathDir = path.join(tmp, 'pathbin');
fs.mkdirSync(pathDir, { recursive: true });
const onPathBin = path.join(pathDir, 'Holmake');
fs.writeFileSync(onPathBin, '#!/bin/sh\nexit 0\n');
fs.chmodSync(onPathBin, 0o755);

const emptyDir = path.join(tmp, 'empty');
fs.mkdirSync(emptyDir, { recursive: true });

const SRC = path.join(tmp, 'proj', 'src');
const DOC = { uri: vscodeStub.Uri.file(path.join(SRC, 'fooScript.sml')) };
const OTHER_SRC = path.join(tmp, 'proj', 'other');
const OTHER_DOC =
  { uri: vscodeStub.Uri.file(path.join(OTHER_SRC, 'barScript.sml')) };

const origPath = process.env.PATH;

// Build a Holmake whose `holdir' is whatever the test wants now, and
// retire the previous one so its listener stops hearing events.
let live = null;
function holmake(dir) {
  if (live) { live.dispose(); }
  live = new Holmake(() => dir);
  return live;
}

(async () => {
  // ---- the fix ------------------------------------------------------
  reset();
  process.env.PATH = emptyDir;
  await holmake(holdir).run(DOC);
  check('one task is executed', executed.length === 1, executed.length);
  const task = executed[0] && executed[0].task;
  const pres = (task && task.presentationOptions) || {};
  check('the terminal is not closed when the task ends',
        pres.close === false, pres.close);
  check('it gets a panel of its own, reused across runs',
        pres.panel === vscodeStub.TaskPanelKind.Dedicated, pres.panel);
  check('it is revealed without stealing focus',
        pres.reveal === vscodeStub.TaskRevealKind.Always &&
          pres.focus === false, pres);
  check('a rerun starts from a clear terminal and echoes the command',
        pres.clear === true && pres.echo === true, pres);
  check('the reuse message says how to dismiss it',
        pres.showReuseMessage === true, pres.showReuseMessage);
  // The negative that pins the regression: no terminal, so no
  // `shellPath' can creep back in.
  check('no terminal is created at all', terminals.length === 0, terminals);

  // ---- where it runs ------------------------------------------------
  check('it runs a process, not a shell command',
        task.execution instanceof ProcessExecution, task.execution);
  check('it runs the Holmake under holdir',
        task.execution.process === holmakeBin, task.execution.process);
  check('it runs in the document\'s directory, not on the document',
        task.execution.options.cwd === SRC, task.execution.options);
  check('the directory is in the definition, which keys the panel',
        task.definition.type === 'holmake' &&
          task.definition.directory === SRC, task.definition);
  check('with no containing folder the task is workspace-scoped',
        task.scope === vscodeStub.TaskScope.Workspace, task.scope);

  reset();
  folder = { name: 'proj', uri: vscodeStub.Uri.file(path.join(tmp, 'proj')) };
  await holmake(holdir).run(DOC);
  check('a file inside a folder is scoped to that folder',
        executed[0].task.scope === folder, executed[0].task.scope);

  // ---- the settings -------------------------------------------------
  reset();
  settings['holmake.args'] = ['-j4'];
  await holmake(holdir).run(DOC);
  check('hol4-mode.holmake.args reach the command unchanged',
        JSON.stringify(executed[0].task.execution.args) ===
          JSON.stringify(['-j4']), executed[0].task.execution.args);

  reset();
  settings['holmake.executable'] = '/elsewhere/Holmake';
  await holmake(holdir).run(DOC);
  check('hol4-mode.holmake.executable wins over holdir',
        executed[0].task.execution.process === '/elsewhere/Holmake',
        executed[0].task.execution.process);

  // ---- finding Holmake ----------------------------------------------
  reset();
  process.env.PATH = pathDir;
  await holmake(undefined).run(DOC);
  check('with no holdir, a Holmake on the PATH is used',
        executed.length === 1 &&
          executed[0].task.execution.process === 'Holmake',
        executed.map((e) => e.task.execution.process));

  reset();
  process.env.PATH = emptyDir;
  await holmake(undefined).run(DOC);
  check('with no holdir and nothing on the PATH, nothing is run',
        executed.length === 0, executed.length);
  check('and the message names what would have said where HOL is',
        errors.length === 1 && /hol4-mode\.holdir/.test(errors[0]), errors);

  // ---- what it says when it ends ------------------------------------
  reset();
  process.env.PATH = emptyDir;
  const ok = holmake(holdir);
  await ok.run(DOC);
  fireEnd({ execution: executed[0].exec, exitCode: 0 });
  check('a clean run raises no popup', errors.length === 0 &&
        infos.length === 0, { errors, infos });
  check('it says so in the status bar and the log',
        statuses.length === 1 &&
          channelLines.some((l) => /succeeded/.test(l)),
        { statuses, channelLines });

  // ---- which panel a failure leaves you looking at -------------------
  // The Output view and the Terminal view are one slot at the bottom
  // of the window, so revealing `HOL: Editor' -- whose entire
  // contribution is a line naming the exit code -- buries the
  // terminal, which holds the compiler messages saying where the
  // build actually broke.
  //
  // The positive control comes first, and has to: it proves the stub
  // really records `show()' and that the `firstError' latch really
  // is fresh in this block.  Without it a recorder that never fired
  // would be indistinguishable from a bug that was fixed.
  reset();
  process.env.PATH = emptyDir;
  await holmake(undefined).run(DOC);
  check('a refusal, which has no terminal to show instead, reveals the log',
        channel('HOL: Editor').shows.length === 1,
        channel('HOL: Editor').shows);
  check('and reveals it without taking focus',
        channel('HOL: Editor').shows[0] === true,
        channel('HOL: Editor').shows);

  reset();
  const bad = holmake(holdir);
  await bad.run(DOC);
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a failed run is reported, with its directory and its code',
        errors.length === 1 && errors[0].includes(SRC) &&
          errors[0].includes('2'), errors);
  check('and is written to the log as an error',
        channel('HOL: Editor').lines.some(
          (l) => /^Error: Holmake failed/.test(l)),
        channel('HOL: Editor').lines);
  check('but the log is not brought forward over the terminal',
        channel('HOL: Editor').shows.length === 0,
        channel('HOL: Editor').shows);

  reset();
  const killed = holmake(holdir);
  await killed.run(DOC);
  // `exitCode' is undefined when the task was *terminated* -- the
  // user pressing the trash can must not be told their build failed.
  fireEnd({ execution: executed[0].exec, exitCode: undefined });
  check('a run the user stopped is not an error', errors.length === 0,
        errors);
  check('but it is still noted', channelLines.some((l) => /stopped/.test(l)),
        channelLines);

  // `onDidEndTaskProcess' is window-wide: npm, make, everyone's tasks
  // arrive at the same handler.
  reset();
  const quiet = holmake(holdir);
  await quiet.run(DOC);
  const before = channelLines.length;
  fireEnd({ execution: { task: { definition: { type: 'npm' } } },
            exitCode: 1 });
  check('another extension\'s task is ignored',
        errors.length === 0 && channelLines.length === before,
        { errors, added: channelLines.slice(before) });

  // ---- the terminal a failure puts back in front --------------------
  // Identified by process id: a terminal's name is UI text VS Code
  // composes from the task, and `Holmake (src)' does not pick out
  // one directory in a tree with as many `src's as HOL has.
  reset();
  const byPid = openTerminal(fakeTerminal(4242));
  const failing = holmake(holdir);
  await failing.run(DOC);
  fireStart({ execution: executed[0].exec, processId: 4242 });
  await settle();
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a failed run brings its own terminal back to the front',
        byPid.shows.length === 1, byPid.shows);
  check('and does that without taking focus either',
        byPid.shows[0] === true, byPid.shows);

  // A pid no terminal admits to -- the documented type of
  // `Terminal.processId' allows `undefined' -- still leaves the one
  // terminal that opened while the run was starting.
  reset();
  const unknown = holmake(holdir);
  await unknown.run(DOC);
  const byOpening = openTerminal(fakeTerminal(undefined));
  fireStart({ execution: executed[0].exec, processId: 999 });
  await settle();
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a terminal that will not name its process is found by having ' +
        'opened for the run', byOpening.shows.length === 1,
        byOpening.shows);

  reset();
  const unidentified = holmake(holdir);
  await unidentified.run(DOC);
  const bystander = openTerminal(fakeTerminal(7));
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a failure that never identified a terminal shows none',
        bystander.shows.length === 0, bystander.shows);
  check('and still reports itself', errors.length === 1, errors);

  reset();
  const closed = holmake(holdir);
  await closed.run(DOC);
  const gone = openTerminal(fakeTerminal(11));
  fireStart({ execution: executed[0].exec, processId: 11 });
  await settle();
  closeTerminal(gone);
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a terminal the user has closed is not shown again',
        gone.shows.length === 0, gone.shows);

  reset();
  const clean = holmake(holdir);
  await clean.run(DOC);
  const quietTerm = openTerminal(fakeTerminal(13));
  fireStart({ execution: executed[0].exec, processId: 13 });
  await settle();
  fireEnd({ execution: executed[0].exec, exitCode: 0 });
  check('a clean run reveals neither the log nor the terminal',
        channel('HOL: Editor').shows.length === 0 &&
          quietTerm.shows.length === 0,
        { log: channel('HOL: Editor').shows, term: quietTerm.shows });

  // ---- one at a time, per directory ---------------------------------
  reset();
  const busy = holmake(holdir);
  await busy.run(DOC);
  await busy.run(DOC);
  check('a second run in the same directory does not start',
        executed.length === 1, executed.length);
  check('and says why', infos.length === 1 && infos[0].includes(SRC), infos);
  await busy.run(OTHER_DOC);
  check('but another directory is free to build',
        executed.length === 2, executed.length);
  fireEnd({ execution: executed[0].exec, exitCode: 0 });
  await busy.run(DOC);
  check('and the first directory is free again once it has finished',
        executed.length === 3, executed.length);

  // ---- documents with no directory ----------------------------------
  reset();
  await holmake(holdir).run({ uri: { scheme: 'untitled',
                                     fsPath: 'Untitled-1' } });
  check('an unsaved buffer builds nothing', executed.length === 0,
        executed.length);
  check('and is told to be saved first', errors.length === 1, errors);

  // ---- when a task cannot be started --------------------------------
  // `executeTask' is documented to throw where no process can be
  // started.  The fallback terminal has no `shellPath', so its root
  // process is a shell, which outlives Holmake -- the bug is not
  // reintroduced on the way out.
  reset();
  executeThrows = true;
  await holmake(holdir).run(DOC);
  check('a task that cannot start falls back to a terminal',
        terminals.length === 1, terminals);
  check('and that terminal is a shell, not Holmake itself',
        terminals.length === 1 && terminals[0].shellPath === undefined,
        terminals[0]);

  process.env.PATH = origPath;
  console.log(failed === 0 ? '\nall checks passed'
                           : `\n${failed} check(s) failed`);
  fs.rmSync(tmp, { recursive: true, force: true });
  process.exit(failed === 0 ? 0 : 1);
})();
