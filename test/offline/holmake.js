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
let channelLines = [];      // the HOL: Editor channel
let settings = {};          // hol4-mode.* configuration
let folder = undefined;     // what getWorkspaceFolder answers
let executeThrows = false;

function reset() {
  executed = []; terminals = []; errors = []; infos = [];
  statuses = []; channelLines = []; settings = {};
  folder = undefined; executeThrows = false;
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
    createOutputChannel: () => ({
      appendLine(l) { channelLines.push(l); }, show() {}, dispose() {},
    }),
    showErrorMessage: (m) => { errors.push(m); },
    showInformationMessage: (m) => { infos.push(m); },
    setStatusBarMessage: (m) => { statuses.push(m); },
    createTerminal: (opts) => {
      terminals.push(opts);
      return { sendText() {}, show() {}, dispose() {} };
    },
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
    onDidEndTaskProcess: (fn) => {
      endHandlers.push(fn);
      return { dispose() {
        const i = endHandlers.indexOf(fn);
        if (i >= 0) { endHandlers.splice(i, 1); }
      } };
    },
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

const { Holmake } = require(path.join(REPO, 'out/holmake.js'));

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

  reset();
  const bad = holmake(holdir);
  await bad.run(DOC);
  fireEnd({ execution: executed[0].exec, exitCode: 2 });
  check('a failed run is reported, with its directory and its code',
        errors.length === 1 && errors[0].includes(SRC) &&
          errors[0].includes('2'), errors);

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
