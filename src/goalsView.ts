import * as vscode from 'vscode';
import { escapeHtml } from './server';
import {
    GoalStateParams,
    GoalStateResponse,
    LspClients,
    isHolScript,
} from './lspClient';

const DEBOUNCE_MS = 150;

/** Side-pane webview rendering `$/hol/goalState' for the cursor
 * position; refreshed on debounced selection/editor changes. */
export class GoalsView implements vscode.Disposable {
    private panel: vscode.WebviewPanel | undefined;
    private timer: NodeJS.Timeout | undefined;
    private readonly disposables: vscode.Disposable[] = [];

    constructor(private readonly clients: LspClients) {
        this.disposables.push(
            vscode.window.onDidChangeTextEditorSelection(
                (e) => this.schedule(e.textEditor)),
            vscode.window.onDidChangeActiveTextEditor(
                (ed) => { if (ed) this.schedule(ed); }),
            // A server takes seconds to load its heap; refresh when
            // it comes up rather than leaving the pane on "starting"
            // until the next keystroke.
            this.clients.onDidChangeClientState(() => {
                const ed = vscode.window.activeTextEditor;
                if (ed) this.schedule(ed);
            }));
    }

    toggle(): void {
        if (this.panel) {
            this.panel.dispose();
            return;
        }
        this.panel = vscode.window.createWebviewPanel(
            'hol4.goalsPane',
            'HOL Goals',
            { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
            { retainContextWhenHidden: true });
        this.panel.onDidDispose(() => {
            if (this.timer) clearTimeout(this.timer);
            this.timer = undefined;
            this.panel = undefined;
        });
        this.renderIdle('Move the cursor into a Proof … QED body to see goals.');
        if (vscode.window.activeTextEditor) {
            this.schedule(vscode.window.activeTextEditor);
        }
    }

    dispose(): void {
        if (this.timer) clearTimeout(this.timer);
        for (const d of this.disposables) d.dispose();
        if (this.panel) this.panel.dispose();
    }

    private schedule(editor: vscode.TextEditor): void {
        if (!this.panel) return;
        // Only scripts have a server, and so a goal state.
        if (!isHolScript(editor.document)) return;
        if (this.timer) clearTimeout(this.timer);
        this.timer = setTimeout(() => this.refresh(editor), DEBOUNCE_MS);
    }

    private async refresh(editor: vscode.TextEditor): Promise<void> {
        if (!this.panel) return;
        const doc = editor.document;
        // Nothing in this file has been compiled, so there is no goal
        // state anywhere in it.  Say why, rather than letting the
        // request come back null and reporting "no goal state at this
        // position" -- which would send the user looking for the fault
        // in their proof.
        const blocked = this.clients.blockedFor(doc);
        if (blocked) {
            this.renderIdle(`Not compiling this file: ${blocked}. ` +
                'Build the dependency, then edit the Ancestors / Libs ' +
                'header (or run "HOL: Compile the active script again").');
            return;
        }
        const pos = editor.selection.active;
        // VS Code positions are UTF-16 code units; server expects
        // UTF-8 byte offsets, so a line containing ∀ / ‘’ / ⇒ etc.
        // otherwise lands the walker on the wrong step.
        const params: GoalStateParams = {
            textDocument: { uri: doc.uri.toString() },
            position: {
                line: pos.line,
                character: utf16ToUtf8ByteOffset(doc, pos.line, pos.character),
            },
        };
        let reply: GoalStateResponse | null | undefined;
        try {
            // Resolved per document: each script has its own server.
            reply = await this.clients.sendRequest<GoalStateResponse | null>(
                doc, '$/hol/goalState', params);
        } catch (err) {
            this.renderIdle(`goalState request failed: ${err}`);
            return;
        }
        if (!this.panel) return;
        if (reply === undefined) {
            this.renderIdle('Starting the HOL server for this file…');
            return;
        }
        this.render(reply);
    }

    private render(reply: GoalStateResponse | null): void {
        if (!reply) {
            this.renderIdle('No goal state at this position.');
            return;
        }
        if (reply.status === 'pending') {
            this.renderIdle('Compile in progress — goal state pending.');
            return;
        }
        if (reply.error) {
            this.renderStatus(reply, `<div class="err">${escapeHtml(reply.error)}</div>`);
            return;
        }
        if (reply.pretty && reply.pretty.length > 0) {
            this.renderStatus(reply,
                `<pre class="pretty">${ansiToHtml(reply.pretty)}</pre>`);
            return;
        }
        const goals = reply.goals ?? [];
        if (goals.length === 0) {
            this.renderStatus(reply, '<div class="ok">No open goals.</div>');
            return;
        }
        const rows = goals.map((g, i) => {
            // HOL convention: reverse the array so the oldest
            // assumption sits at index [0] at the top.
            const asms = (g.asms ?? []).slice().reverse().map((a, n) =>
                `<div class="asm">[${n}]&nbsp;&nbsp;${escapeHtml(a)}</div>`).join('');
            const hdr = goals.length > 1
                ? `Goal ${i + 1} of ${goals.length}` : `Goal ${i + 1}`;
            return `
                <div class="goal">
                  <div class="hdr">${hdr}</div>
                  ${asms ? `<div class="asms">${asms}</div>` : ''}
                  <div class="concl">${escapeHtml(g.goal)}</div>
                </div>`;
        }).join('');
        this.renderStatus(reply, rows);
    }

    private renderStatus(reply: GoalStateResponse, body: string): void {
        const stepInfo = reply.step != null
            ? `<span class="step">step ${reply.step}</span>` : '';
        const opaque = reply.opaque ? '<span class="opaque">(opaque)</span>' : '';
        const thm = reply.theorem ? escapeHtml(reply.theorem) : '';
        const header = thm
            ? `<div class="thm">${thm} ${stepInfo} ${opaque}</div>` : '';
        this.setHtml(`${header}${body}`);
    }

    private renderIdle(message: string): void {
        this.setHtml(`<div class="idle">${escapeHtml(message)}</div>`);
    }

    private setHtml(body: string): void {
        if (!this.panel) return;
        this.panel.webview.html = wrap(body);
    }
}

function utf16ToUtf8ByteOffset(
    doc: vscode.TextDocument,
    line: number,
    character: number
): number {
    if (line < 0 || line >= doc.lineCount) return character;
    const prefix = doc.lineAt(line).text.substring(0, character);
    return Buffer.byteLength(prefix, 'utf8');
}

/** Translate the VT100 SGR escapes HOL's `PPBackEnd.vt100_terminal`
 * emits into inline HTML spans.  Handles reset (0), bold (1), and
 * 8-colour foreground (30-37 / 90-97). */
function ansiToHtml(input: string): string {
    const parts = input.split(/\x1B\[([0-9;]*)m/);
    let openSpans = 0;
    let out = '';
    for (let i = 0; i < parts.length; i++) {
        if (i % 2 === 0) {
            out += escapeHtml(parts[i]);
        } else {
            const codes = parts[i].split(';').map(s => parseInt(s, 10) || 0);
            for (const code of codes) {
                if (code === 0) {
                    while (openSpans > 0) { out += '</span>'; openSpans--; }
                } else {
                    const cls = sgrClass(code);
                    if (cls !== undefined) {
                        out += `<span class="${cls}">`;
                        openSpans++;
                    }
                }
            }
        }
    }
    while (openSpans > 0) { out += '</span>'; openSpans--; }
    return out;
}

function sgrClass(code: number): string | undefined {
    if (code === 1) return 'ansi-bold';
    if (code >= 30 && code <= 37) return `ansi-fg-${code - 30}`;
    if (code >= 90 && code <= 97) return `ansi-fg-b${code - 90}`;
    return undefined;
}

function wrap(body: string): string {
    return `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"><style>
  body { font-family: var(--vscode-editor-font-family, monospace);
         font-size: var(--vscode-editor-font-size, 13px);
         color: var(--vscode-editor-foreground);
         margin: 0.5em; }
  .thm { font-weight: bold; margin-bottom: 0.5em;
         color: var(--vscode-symbolIcon-classForeground); }
  .step { font-weight: normal;
          color: var(--vscode-descriptionForeground); }
  .opaque { font-weight: normal;
            color: var(--vscode-editorWarning-foreground); }
  .goal { margin-bottom: 1em; }
  .hdr { color: var(--vscode-descriptionForeground);
         font-size: 0.9em; margin-bottom: 0.2em; }
  .asms { padding-left: 0.5em; margin-bottom: 0.3em; }
  .asm { white-space: pre-wrap; }
  .concl { white-space: pre-wrap;
           border-top: 2px solid var(--vscode-editor-foreground);
           padding-top: 0.4em; margin-top: 0.4em; }
  .err { color: var(--vscode-editorError-foreground);
         white-space: pre-wrap; }
  .ok, .idle { color: var(--vscode-descriptionForeground); }
  pre.pretty { margin: 0; white-space: pre-wrap;
               font-family: inherit; font-size: inherit; }
  .ansi-bold { font-weight: bold; }
  .ansi-fg-0  { color: #808080; }
  .ansi-fg-1  { color: var(--vscode-terminal-ansiRed, #cd3131); }
  .ansi-fg-2  { color: var(--vscode-terminal-ansiGreen, #0dbc79); }
  .ansi-fg-3  { color: var(--vscode-terminal-ansiYellow, #e5e510); }
  .ansi-fg-4  { color: var(--vscode-terminal-ansiBlue, #2472c8); }
  .ansi-fg-5  { color: var(--vscode-terminal-ansiMagenta, #bc3fbc); }
  .ansi-fg-6  { color: var(--vscode-terminal-ansiCyan, #11a8cd); }
  .ansi-fg-7  { color: var(--vscode-terminal-ansiWhite, #e5e5e5); }
  .ansi-fg-b0 { color: var(--vscode-terminal-ansiBrightBlack, #666666); }
  .ansi-fg-b1 { color: var(--vscode-terminal-ansiBrightRed, #f14c4c); }
  .ansi-fg-b2 { color: var(--vscode-terminal-ansiBrightGreen, #23d18b); }
  .ansi-fg-b3 { color: var(--vscode-terminal-ansiBrightYellow, #f5f543); }
  .ansi-fg-b4 { color: var(--vscode-terminal-ansiBrightBlue, #3b8eea); }
  .ansi-fg-b5 { color: var(--vscode-terminal-ansiBrightMagenta, #d670d6); }
  .ansi-fg-b6 { color: var(--vscode-terminal-ansiBrightCyan, #29b8db); }
  .ansi-fg-b7 { color: var(--vscode-terminal-ansiBrightWhite, #ffffff); }
</style></head><body>${body}</body></html>`;
}
