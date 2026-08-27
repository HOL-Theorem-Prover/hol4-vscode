import * as path from 'path';
import * as fs from 'fs';
import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    State,
} from 'vscode-languageclient/node';
import { error } from './common';

/**
 * Shape of the tiny slice of `LanguageClient` we monkey-patch.
 * Kept narrow so future dep upgrades that break these hooks surface
 * as compile errors rather than silent behaviour changes.
 */
interface PatchableConnection {
    initialize(params: unknown): Promise<{
        capabilities?: { positionEncoding?: unknown }
    }>;
}
interface PatchableClient {
    createConnection?: (...args: unknown[]) => Promise<PatchableConnection>;
}

/** Strip server-advertised `positionEncoding` so v9 client accepts
 * a utf-8-declaring server.  Client falls back to its utf-16
 * default; positions on non-ASCII lines are then translated on
 * demand by callers (see goalsView.utf16ToUtf8ByteOffset).
 * Must be applied to every client we create: it only misbehaves on
 * lines carrying non-ASCII, which in HOL is most interesting
 * lines (`‘…’`, `⇒`, `∀`). */
function patchConnectionForPositionEncoding(client: LanguageClient): void {
    const patch = client as unknown as PatchableClient;
    const origCreateConnection = patch.createConnection?.bind(patch);
    if (typeof origCreateConnection !== 'function') return;
    patch.createConnection = async (...args: unknown[]) => {
        const conn = await origCreateConnection(...args);
        const origInitialize = conn.initialize.bind(conn);
        conn.initialize = async (params: unknown) => {
            const result = await origInitialize(params);
            if (result?.capabilities?.positionEncoding !== undefined) {
                delete result.capabilities.positionEncoding;
            }
            return result;
        };
        return conn;
    };
}

/** Position argument for the `$/hol/goalState` custom request. */
export interface GoalStatePosition {
    line: number;
    character: number;
}

export interface GoalStateParams {
    textDocument: { uri: string };
    position: GoalStatePosition;
}

export interface Goal {
    asms: string[];
    goal: string;
}

export interface GoalStateResponse {
    theorem?: string;
    step?: number;
    goals?: Goal[];
    /** Server-side pretty-printed rendering with VT100 ANSI colour
     * escapes.  Present since the goalState LSP extension shipped;
     * preferred over `goals` when non-empty. */
    pretty?: string;
    status?: string;
    opaque?: boolean;
    error?: string;
}

function resolveHolExecutable(fallbackHoldir: string): string | undefined {
    const cfg = vscode.workspace.getConfiguration('hol4-mode');
    const override = cfg.get<string>('lsp.executable');
    if (override && override.trim() !== '') return override;
    if (fallbackHoldir) return path.join(fallbackHoldir, 'bin', 'hol');
    return undefined;
}

/**
 * Does this document get its own `bin/hol lsp` process?
 *
 * Only theory scripts do.  A `.sig` or a plain `.sml` declares no
 * theory of its own, has no goal states, and would cost a heap and a
 * compile for nothing; the server ignores them for binding purposes
 * too.  `untitled:` documents are excluded because they have no
 * directory, and the server picks its heap from the `Holmakefile` in
 * its working directory.
 */
export function isHolScript(doc: vscode.TextDocument): boolean {
    return doc.uri.scheme === 'file' && doc.uri.fsPath.endsWith('Script.sml');
}

/** `DocumentFilter.pattern` is matched as a glob, so a path holding
 * glob metacharacters could match a *different* file and let that
 * file be adopted into this file's server.  Wrap each metacharacter
 * in a one-element character class, which vscode's glob parser reads
 * as a literal.  `]` needs no escape: with every `[` escaped, no
 * character class is ever opened. */
function globEscape(p: string): string {
    return p.replace(/[*?{[]/g, (c) => `[${c}]`);
}

interface ScriptClient {
    client: LanguageClient;
    output: vscode.OutputChannel;
    /** `onDidChangeState` subscription; lives and dies with the client. */
    state: vscode.Disposable;
}

function disposeScriptClient(entry: ScriptClient): void {
    entry.state.dispose();
    // Each server holds a HOL heap, so a leaked process is hundreds
    // of megabytes, not a rounding error.
    entry.client.stop()
        .catch(() => { /* best-effort */ })
        .then(() => entry.output.dispose());
}

/**
 * One `bin/hol lsp` process per theory script, created lazily when a
 * script first becomes visible and disposed when it is closed.
 *
 * A server can serve exactly one script for its lifetime, and this is
 * not a limitation to be worked around later.  Putting a theory in
 * the graph means loading it, and loading it *seals* it
 * (`Theory.load_complete` calls `Thm.mark_sealed`, which writes to
 * the process-global `KernelSig.sealed_ref` deliberately kept outside
 * the snapshot/restore machinery, as a soundness gate against
 * cross-theory redefinition).  A second script's ancestors can
 * therefore be neither re-read nor withdrawn.  A shared server does
 * not fail loudly: it answers with wrong goal states and dead hovers.
 * See `tools-poly/lsp/README.md`, "One server per buffer", in the HOL
 * repo.
 */
export class LspClients implements vscode.Disposable {
    private readonly clients = new Map<string, ScriptClient>();
    private readonly status: vscode.StatusBarItem;
    private readonly disposables: vscode.Disposable[] = [];
    private readonly stateChanged = new vscode.EventEmitter<void>();
    private exe: string | undefined;

    /** Fires when any client starts, stops, or is disposed.  A server
     * takes seconds to load its heap, so consumers that asked too
     * early need a nudge rather than a poll. */
    readonly onDidChangeClientState = this.stateChanged.event;

    constructor(private readonly holdir: string) {
        this.status = vscode.window.createStatusBarItem(
            vscode.StatusBarAlignment.Left, 100);
        this.status.command = 'hol4-mode.lsp.showOutput';
    }

    start(): void {
        const exe = resolveHolExecutable(this.holdir);
        if (!exe) {
            error('LSP: no `bin/hol` path resolved from ' +
                'hol4-mode.lsp.executable, hol4-mode.holdir, or $HOLDIR');
            this.showStatus('HOL LSP: no executable', true);
            return;
        }
        if (!fs.existsSync(exe)) {
            error(`LSP: ${exe} does not exist`);
            this.showStatus('HOL LSP: exe missing', true);
            return;
        }
        this.exe = exe;

        this.disposables.push(
            // Visible, not open: a window restoring twenty tabs would
            // otherwise start twenty heaps at once.  A script gets its
            // server the moment it is actually looked at.
            vscode.window.onDidChangeVisibleTextEditors(
                () => this.syncVisibleEditors()),
            vscode.window.onDidChangeActiveTextEditor(
                () => this.refreshStatus()),
            vscode.workspace.onDidCloseTextDocument(
                (doc) => this.closed(doc)));
        this.syncVisibleEditors();
    }

    /** Restart the server for the active editor's script. */
    async restartActive(): Promise<void> {
        const doc = vscode.window.activeTextEditor?.document;
        if (!doc || !isHolScript(doc)) {
            vscode.window.showInformationMessage(
                'HOL LSP: the active editor is not a HOL theory script.');
            return;
        }
        const entry = this.clients.get(doc.uri.toString());
        if (!entry) {
            this.ensure(doc);
            return;
        }
        try {
            await entry.client.stop();
            await entry.client.start();
        } catch (err) {
            error(`LSP failed to restart for ${doc.uri.fsPath}: ${err}`);
        }
        this.refreshStatus();
    }

    /** Show the output channel of the active editor's server, or the
     * only server there is if the active editor has none. */
    showOutput(): void {
        const doc = vscode.window.activeTextEditor?.document;
        const entry = doc ? this.clients.get(doc.uri.toString()) : undefined;
        if (entry) {
            entry.output.show(true);
            return;
        }
        if (this.clients.size === 1) {
            [...this.clients.values()][0].output.show(true);
            return;
        }
        vscode.window.showInformationMessage(this.clients.size === 0
            ? 'HOL LSP: no server is running.'
            : 'HOL LSP: open a theory script to see its server output.');
    }

    /** Send `method` to the server owning `doc`, if it is running. */
    async sendRequest<T>(
        doc: vscode.TextDocument,
        method: string,
        params: unknown
    ): Promise<T | undefined> {
        const entry = this.clients.get(doc.uri.toString());
        if (!entry || entry.client.state !== State.Running) return undefined;
        return entry.client.sendRequest<T>(method, params);
    }

    dispose(): void {
        for (const d of this.disposables) d.dispose();
        this.disposables.length = 0;
        for (const entry of this.clients.values()) disposeScriptClient(entry);
        this.clients.clear();
        this.stateChanged.dispose();
        this.status.dispose();
    }

    private syncVisibleEditors(): void {
        for (const editor of vscode.window.visibleTextEditors) {
            this.ensure(editor.document);
        }
        this.refreshStatus();
    }

    /** Start a client for `doc` if this is its first sighting. */
    private ensure(doc: vscode.TextDocument): void {
        if (!this.exe || !isHolScript(doc)) return;
        const key = doc.uri.toString();
        if (this.clients.has(key)) return;
        const entry = this.create(this.exe, doc);
        // Registered before `start` is kicked off, so a burst of
        // visibility events cannot start two servers for one file.
        this.clients.set(key, entry);
        entry.client.start().catch((err) => {
            error(`LSP failed to start for ${doc.uri.fsPath}: ${err}`);
            this.refreshStatus();
        });
    }

    private create(exe: string, doc: vscode.TextDocument): ScriptClient {
        const fsPath = doc.uri.fsPath;
        const rel = vscode.workspace.asRelativePath(doc.uri);
        const output = vscode.window.createOutputChannel(`HOL4 LSP: ${rel}`);

        // No `transport:` field: the client defaults to stdio without
        // appending the `--stdio` flag that `bin/hol lsp` rejects.
        const serverOptions: ServerOptions = { command: exe, args: ['lsp'] };

        const clientOptions: LanguageClientOptions = {
            // Pinned to this one path.  Selecting by language would
            // let the client's `register` sweep over
            // `workspace.textDocuments` adopt every other open SML
            // document into this process, which is exactly the
            // sharing that yields wrong goal states.
            documentSelector: [{ scheme: 'file', pattern: globEscape(fsPath) }],
            // Sharing the name keeps the Problems panel reading
            // "hol4-lsp" for every file; the collections themselves
            // stay one per client, each owning its own URI.
            diagnosticCollectionName: 'hol4-lsp',
            outputChannel: output,
            // No `synchronize.fileEvents`: the server has no
            // `workspace/didChangeWatchedFiles` handler and logs the
            // notification as unknown, and one workspace-wide watcher
            // per open script would be pure overhead.
        };

        const client = new LanguageClient(
            `hol4-lsp:${fsPath}`, `HOL4 LSP: ${rel}`,
            serverOptions, clientOptions);
        patchConnectionForPositionEncoding(client);
        const state = client.onDidChangeState(() => {
            this.refreshStatus();
            this.stateChanged.fire();
        });
        return { client, output, state };
    }

    private closed(doc: vscode.TextDocument): void {
        const key = doc.uri.toString();
        const entry = this.clients.get(key);
        if (!entry) return;
        this.clients.delete(key);
        disposeScriptClient(entry);
        this.refreshStatus();
        this.stateChanged.fire();
    }

    /** The status bar reports the active editor's server: with N of
     * them, that is the only one the user is looking at. */
    private refreshStatus(): void {
        const doc = vscode.window.activeTextEditor?.document;
        if (!doc || !isHolScript(doc)) {
            this.status.hide();
            return;
        }
        if (!this.exe) {
            this.showStatus('HOL LSP: no executable', true);
            return;
        }
        const entry = this.clients.get(doc.uri.toString());
        if (!entry) {
            this.showStatus('HOL LSP: not started', true);
            return;
        }
        switch (entry.client.state) {
            case State.Running:
                this.showStatus('HOL LSP', false);
                break;
            case State.Starting:
                this.showStatus('HOL LSP: starting…', false);
                break;
            default:
                this.showStatus('HOL LSP: stopped', true);
                break;
        }
    }

    private showStatus(text: string, warn: boolean): void {
        this.status.text = warn ? `$(warning) ${text}` : `$(check) ${text}`;
        this.status.tooltip =
            'HOL4 LSP for the active script; click for its output channel';
        this.status.show();
    }
}
