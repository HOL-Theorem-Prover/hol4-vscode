import * as path from 'path';
import * as fs from 'fs';
import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    State,
} from 'vscode-languageclient/node';
import { KERNEL_ID, error } from './common';

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
 * demand by callers (see goalsView.utf16ToUtf8ByteOffset). */
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

export class LspClient implements vscode.Disposable {
    private client: LanguageClient | undefined;
    private readonly output: vscode.OutputChannel;
    private readonly status: vscode.StatusBarItem;
    private readonly disposables: vscode.Disposable[] = [];

    constructor(private readonly holdir: string) {
        this.output = vscode.window.createOutputChannel('HOL4 LSP');
        this.status = vscode.window.createStatusBarItem(
            vscode.StatusBarAlignment.Left, 100);
        this.status.command = 'hol4-mode.lsp.showOutput';
    }

    async start(): Promise<void> {
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

        // No `transport:` field: the client defaults to stdio without
        // appending the `--stdio` flag that `bin/hol lsp` rejects.
        const serverOptions: ServerOptions = { command: exe, args: ['lsp'] };
        const clientOptions: LanguageClientOptions = {
            // vscode-languageclient's DocumentSelector type is
            // distinct from the vscode API's, so we inline the
            // literal rather than reusing `hol4selector`.
            documentSelector: [
                { scheme: 'file', language: KERNEL_ID },
                { scheme: 'untitled', language: KERNEL_ID },
            ],
            synchronize: {
                fileEvents: vscode.workspace.createFileSystemWatcher('**/*.{sml,sig}'),
            },
            outputChannel: this.output,
        };

        this.client = new LanguageClient(
            'hol4-lsp', 'HOL4 LSP', serverOptions, clientOptions);
        patchConnectionForPositionEncoding(this.client);
        this.disposables.push(this.client.onDidChangeState(e => {
            if (e.newState === State.Running) {
                this.showStatus('HOL LSP', false);
            } else if (e.newState === State.Stopped) {
                this.showStatus('HOL LSP: stopped', true);
            } else {
                this.showStatus('HOL LSP: starting…', false);
            }
        }));

        try {
            await this.client.start();
        } catch (err) {
            error(`LSP failed to start: ${err}`);
            this.showStatus('HOL LSP: failed', true);
        }
    }

    async restart(): Promise<void> {
        if (this.client) {
            await this.client.stop();
            await this.client.start();
        } else {
            await this.start();
        }
    }

    showOutput(): void {
        this.output.show(true);
    }

    async sendRequest<T>(method: string, params: unknown): Promise<T | undefined> {
        if (!this.client || this.client.state !== State.Running) return undefined;
        return this.client.sendRequest<T>(method, params);
    }

    dispose(): void {
        for (const d of this.disposables) d.dispose();
        this.status.dispose();
        if (this.client) {
            this.client.stop().catch(() => { /* best-effort */ });
        }
    }

    private showStatus(text: string, warn: boolean): void {
        this.status.text = warn ? `$(warning) ${text}` : `$(check) ${text}`;
        this.status.tooltip = 'Click to open the HOL4 LSP output channel';
        this.status.show();
    }
}
