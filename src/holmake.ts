import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { error, log } from './common';

/**
 * Running `Holmake` from the editor, and saying how it went.
 *
 * The command used to be a terminal whose *shell* was Holmake:
 * `createTerminal({shellPath: 'Holmake'})`.  A terminal dies with its
 * root process, so the panel -- and everything Holmake had printed
 * into it -- went the moment Holmake exited.  A build that failed, a
 * build that succeeded, and a `Holmake` that was not installed at all
 * then looked exactly alike: output flickered past and the terminal
 * vanished.  A terminal cannot report an exit code either;
 * `Terminal.exitStatus` is the *shell's* status, readable only while
 * the terminal is closing.
 *
 * A task instead.  VS Code owns the terminal, keeps it after the
 * child exits unless told otherwise, and reports the child's own exit
 * code through `tasks.onDidEndTaskProcess`.  The output is still
 * produced in a real pty, so it looks as it always did.
 */

/** The type our tasks carry in their definition.
 *
 * Nothing is contributed under `contributes.taskDefinitions`, and
 * nothing needs to be: that extension point governs what `tasks.json`
 * accepts and what a `TaskProvider` resolves, neither of which is in
 * play for a task built here and handed straight to `executeTask`.
 * Contributing one *without* a provider would be worse than
 * contributing none -- it would offer `"type": "holmake"` in
 * `tasks.json` and then fail to resolve it. */
const HOLMAKE_TYPE = 'holmake';

interface HolmakeTaskDefinition extends vscode.TaskDefinition {
    type: typeof HOLMAKE_TYPE;
    /** The directory Holmake runs in, absolute.
     *
     * In the *definition*, not merely in the execution's `cwd`,
     * because VS Code keys a `Dedicated` task panel on the
     * definition.  That is what makes "the Holmake terminal for
     * src/num" a stable thing a rerun reuses, while a build in
     * another directory gets its own. */
    directory: string;
}

/** Where Holmake was found, or why it was not. */
export type Resolution =
    | { ok: true; command: string; origin: 'setting' | 'holdir' | 'path' }
    | { ok: false; reason: string };

function isExecutable(p: string): boolean {
    try {
        fs.accessSync(p, fs.constants.X_OK);
        return true;
    } catch {
        return false;
    }
}

function onPath(name: string, env: NodeJS.ProcessEnv): boolean {
    for (const dir of (env.PATH ?? '').split(path.delimiter)) {
        if (dir !== '' && isExecutable(path.join(dir, name))) {
            return true;
        }
    }
    return false;
}

/**
 * Which Holmake to run.
 *
 * The PATH is searched here rather than left to the spawn because
 * "not on the PATH" and "finished" used to look identical -- the
 * terminal appeared and vanished either way.  Finding out first turns
 * that into a sentence naming what was tried.
 *
 * `holdir` is the path the extension has already resolved, not a
 * fresh reading of `hol4-mode.holdir`: `initialize` in `extension.ts`
 * is the only place that expands a leading `$` and falls back to
 * `$HOLDIR`, and a second copy of that is how the two come to
 * disagree.
 */
export function resolveHolmake(
    holdir: string | undefined,
    env: NodeJS.ProcessEnv = process.env,
): Resolution {
    const override = vscode.workspace.getConfiguration('hol4-mode')
        .get<string>('holmake.executable');
    if (override && override.trim() !== '') {
        return { ok: true, command: override.trim(), origin: 'setting' };
    }
    const candidate =
        holdir ? path.join(holdir, 'bin', 'Holmake') : undefined;
    if (candidate && isExecutable(candidate)) {
        return { ok: true, command: candidate, origin: 'holdir' };
    }
    if (onPath('Holmake', env)) {
        return { ok: true, command: 'Holmake', origin: 'path' };
    }
    return {
        ok: false,
        reason: candidate
            ? `Holmake: ${candidate} is not there to run, and Holmake ` +
              'is not on the PATH either'
            : 'Holmake: not on the PATH, and neither hol4-mode.holdir ' +
              'nor $HOLDIR says where HOL is installed',
    };
}

/** Extra arguments for every run, from `hol4-mode.holmake.args`. */
export function holmakeArgs(): string[] {
    return vscode.workspace.getConfiguration('hol4-mode')
        .get<string[]>('holmake.args') ?? [];
}

/**
 * The task a run is.
 *
 * Separate from running it so that a test can read back every
 * decision without a task system to execute it.
 */
export function makeHolmakeTask(
    dir: string, command: string, args: string[],
): vscode.Task {
    const definition: HolmakeTaskDefinition =
        { type: HOLMAKE_TYPE, directory: dir };
    // The folder the file lives in, when it lives in one: the task is
    // then attributed to that folder in the UI.  A file outside every
    // folder -- or a window with no folders at all -- falls back to
    // the workspace; `TaskScope.Global` is documented as unsupported.
    // Nothing we need comes from the scope, because `cwd` is set on
    // the execution below.
    const folder = vscode.workspace.getWorkspaceFolder(vscode.Uri.file(dir));
    const task = new vscode.Task(
        definition,
        folder ?? vscode.TaskScope.Workspace,
        `Holmake (${path.basename(dir)})`,
        'HOL',
        // A process, not a shell.  There is then no command line to
        // quote -- a HOLDIR with a space in it is three different
        // quoting problems on three platforms -- no shell startup
        // file to print a banner or fail, and the exit code reported
        // is Holmake's own rather than a shell's.
        new vscode.ProcessExecution(command, args, { cwd: dir }));
    task.detail = dir;
    task.group = vscode.TaskGroup.Build;
    task.isBackground = false;
    task.presentationOptions = {
        // THE FIX.  `false` is already the default, but it is named
        // here because it is the whole point of this file: the
        // terminal outlives the process, so what Holmake printed is
        // still on screen to be read.
        close: false,
        // One terminal per directory, reused across runs.  Shared
        // would interleave Holmake with other extensions' tasks; New
        // would leave a terminal behind for every rebuild.
        panel: vscode.TaskPanelKind.Dedicated,
        // Bring it forward without taking the cursor out of the
        // editor, the same bargain the goals pane strikes.
        reveal: vscode.TaskRevealKind.Always,
        focus: false,
        // Echo the command line.  This replaces the banner the old
        // terminal carried, and says what the banner could not:
        // *which* Holmake is running.
        echo: true,
        // A rerun reads as a rerun, rather than as output appended to
        // the previous run's errors.
        clear: true,
        // "press any key to close it" is exactly the dismissal
        // instruction a user who has just got their output back
        // needs.
        showReuseMessage: true,
    };
    return task;
}

/** POSIX quoting, for the fallback terminal below -- the only path
 * here that builds a command line at all. */
function shellQuote(word: string): string {
    return /^[\w.@%+=:,/-]+$/.test(word)
        ? word : `'${word.replace(/'/g, `'\\''`)}'`;
}

/**
 * Run Holmake from a terminal after all.
 *
 * `executeTask` is documented to throw "in an environment where a new
 * process cannot be started", so there has to be something here.  The
 * terminal is created with no `shellPath`, which is the difference
 * that matters: its root process is a shell, the shell outlives
 * Holmake, and the output stays.  There is no exit code on this path.
 */
function fallbackTerminal(
    dir: string, command: string, args: string[],
): void {
    const terminal = vscode.window.createTerminal({ cwd: dir,
                                                    name: 'Holmake' });
    terminal.sendText([command, ...args].map(shellQuote).join(' '));
    terminal.show(true);
}

/**
 * The Holmake command, and the reporting of what it did.
 *
 * One of these per window, built in `activate`.  The exit-code
 * listener belongs to the object rather than to a run: subscribing
 * per invocation would report the nth exit n times.
 */
export class Holmake implements vscode.Disposable {
    /** Runs in flight, by directory.  The value is `undefined`
     * between claiming the slot and `executeTask` resolving. */
    private readonly running =
        new Map<string, vscode.TaskExecution | undefined>();
    private readonly disposables: vscode.Disposable[] = [];

    constructor(private readonly holdir: () => string | undefined) {
        this.disposables.push(
            vscode.tasks.onDidEndTaskProcess((e) => this.ended(e)));
    }

    async run(doc: vscode.TextDocument): Promise<void> {
        // An unsaved buffer has no directory to build in, and
        // `path.dirname` would invent one from whatever its throwaway
        // name happens to be.
        if (doc.uri.scheme !== 'file') {
            this.refuse('Holmake: save the document first -- an unsaved ' +
                        'buffer has no directory to build in');
            return;
        }
        const dir = path.dirname(doc.uri.fsPath);
        if (this.running.has(dir)) {
            // Two Holmakes in one directory race over the same
            // targets.  Say so rather than starting the second.
            vscode.window.showInformationMessage(
                `Holmake is already running in ${dir}`);
            return;
        }
        const found = resolveHolmake(this.holdir());
        if (!found.ok) {
            this.refuse(found.reason);
            return;
        }
        const args = holmakeArgs();
        // Claim the slot before the await, not after: the await
        // yields, and a second invocation in that window would
        // otherwise start a second run.
        this.running.set(dir, undefined);
        log(`Holmake: ${[found.command, ...args].join(' ')} in ${dir}`);
        try {
            this.running.set(dir, await vscode.tasks.executeTask(
                makeHolmakeTask(dir, found.command, args)));
        } catch (e) {
            this.running.delete(dir);
            error(`Holmake: no task could be started (${e}); falling ` +
                  'back to a terminal, which reports no exit status');
            fallbackTerminal(dir, found.command, args);
        }
    }

    private ended(e: vscode.TaskProcessEndEvent): void {
        const def = e.execution.task.definition;
        // `onDidEndTaskProcess` is a window-wide event: every other
        // extension's tasks end here too.
        if (def.type !== HOLMAKE_TYPE) {
            return;
        }
        const dir = typeof def.directory === 'string' ? def.directory : '';
        this.running.delete(dir);
        if (e.exitCode === 0) {
            // No notification.  The terminal is on screen with the
            // output in it; a popup would only be in the way.
            log(`Holmake: ${dir} succeeded`);
            vscode.window.setStatusBarMessage(
                `Holmake succeeded in ${path.basename(dir)}`, 5000);
        } else if (e.exitCode === undefined) {
            // Undefined means terminated, which is something the user
            // did on purpose.  Not an error.
            log(`Holmake: ${dir} was stopped before it finished`);
        } else {
            const msg = `Holmake failed in ${dir} (exit ${e.exitCode})`;
            error(msg);
            vscode.window.showErrorMessage(msg);
        }
    }

    private refuse(msg: string): void {
        error(msg);
        vscode.window.showErrorMessage(msg);
    }

    dispose(): void {
        // Runs in flight are left alone: the window closing takes
        // their terminals with it, and a deactivation in any other
        // circumstance is no reason to abandon a build.
        this.disposables.forEach((d) => d.dispose());
        this.running.clear();
    }
}
