import * as vscode from 'vscode';
import * as path from 'path';
import { log, error, EXTENSION_ID, KERNEL_ID } from './common';
import { HolNotebook } from './notebook';

/**
 * Get the editors current selection if any, or the contents of the editor's
 * current line otherwise.
 */
function getSelection(editor: vscode.TextEditor): string {
    const document = editor.document;
    const selection = editor.selection;
    return selection.isEmpty ? document.lineAt(selection.active.line).text
        : document.getText(selection);
}

export class HOLExtensionContext {

    /** Currently active notebook editor (if any). */
    public notebook?: HolNotebook;

    constructor(
        private context: vscode.ExtensionContext,

        /** Path to the HOL installation to use. */
        public holPath: string
    ) { }

    /** Returns whether the current session is active. If it is not active, then
     * an error message is printed.
     */
    isActive(): boolean {
        this.sync();
        if (!this.notebook?.kernel.running) {
            vscode.window.showErrorMessage('No active HOL session; doing nothing.');
            error('No active session; doing nothing');
        }

        return !!this.notebook?.kernel.running;
    }

    sync() {
        if (this.notebook && !this.notebook.sync()) {
            this.notebook = undefined;
        }
    }

    /**
     * Start HOL terminal session.
     */
    async startSession(editor: vscode.TextEditor) {
        this.sync();
        if (this.notebook?.kernel.running) {
            vscode.window.showErrorMessage('HOL session already active; doing nothing.');
            error('Session already active; doing nothing');
            return;
        }

        if (this.notebook) {
            this.notebook.stop();
        } else {
            let docPath = path.dirname(editor.document.uri.fsPath);
            let notebookEditor = vscode.window.visibleNotebookEditors.find(e => {
                return e.notebook.metadata.hol || (
                    // Heuristic identification of orphaned HOL windows
                    e.notebook.isUntitled &&
                    e.notebook.cellCount == 0 &&
                    e.notebook.notebookType == 'interactive'
                )
            });
            if (!notebookEditor) {
                const result = await vscode.commands.executeCommand<{ notebookEditor?: vscode.NotebookEditor }>(
                    'interactive.open',
                    { viewColumn: vscode.ViewColumn.Beside, preserveFocus: false },
                    undefined,
                    KERNEL_ID,
                    'HOL4 Session'
                );
                if (!result.notebookEditor) {
                    error('vscode notebook failed to start');
                    return;
                }
                notebookEditor = result.notebookEditor;
                const edit = new vscode.WorkspaceEdit();
                edit.set(notebookEditor.notebook.uri, [
                    vscode.NotebookEdit.updateNotebookMetadata({ hol: true })
                ]);
                vscode.workspace.applyEdit(edit);
            }
            vscode.commands.executeCommand('notebook.selectKernel',
                { notebookEditor, id: KERNEL_ID, extension: EXTENSION_ID }
            );
            this.notebook = new HolNotebook(this.context, docPath, this.holPath, notebookEditor!);

            vscode.window.tabGroups.onDidChangeTabGroups((e) => {
                if (e.closed && notebookEditor!.notebook.isClosed) {
                    this.notebook?.dispose();
                    this.notebook = undefined;
                }
            });
            vscode.window.tabGroups.onDidChangeTabs((e) => {
                if (e.closed && notebookEditor!.notebook.isClosed) {
                    this.notebook?.dispose();
                    this.notebook = undefined;
                }
            });
        }

        this.notebook.show();
        await this.notebook.start();
        log('Started session');
    }

    /**
     * Stop the HOL terminal session.
     */
    stopSession() {
        if (!this.isActive()) {
            return;
        }

        log('Stopped session');
        this.notebook!.close();
    }

    /**
     * Stop the HOL terminal session.
     */
    restartSession(editor: vscode.TextEditor) {
        log('Restarted session');
        this.notebook?.stop();
        this.startSession(editor);
    }

    /**
     * Send interrupt signal to the HolTerminal.
     */
    interrupt() {
        if (!this.isActive()) {
            return;
        }

        log('Interrupted session');
        this.notebook!.kernel.interrupt();
    }

    /**
     * Send selection to the terminal; preprocess to find `open` and `load`
     * calls.
     */
    async sendSelection(editor: vscode.TextEditor) {
        this.sync();
        if (!this.notebook?.kernel.running) {
            await this.startSession(editor);
        }

        const text = getSelection(editor);

        await this.notebook!.send(text, true, true);
    }


    /**
     * Send all text up to and including the current line in the current editor to
     * the terminal.
     */
    async sendUntilCursor(editor: vscode.TextEditor) {
        this.sync();
        if (!this.notebook?.kernel.running) {
            await this.startSession(editor);
        }

        const currentLine = editor.selection.active.line;

        const selection = new vscode.Selection(0, 0, currentLine, 0);
        const text = editor.document.getText(selection);

        await this.notebook!.send(text, true, true);
    }

    /**
     * Toggle printing of terms with or without types.
     */
    async toggleShowTypes() {
        if (!this.printingToggleAvailable()) {
            return;
        }

        await this.notebook!.send('Globals.show_types := not (!Globals.show_types)', false, true);
    }

    /**
     * Toggle printing of theorem hypotheses.
     */
    async toggleShowAssums() {
        if (!this.printingToggleAvailable()) {
            return;
        }
        await this.notebook!.send('Globals.show_assums := not (!Globals.show_assums)', false, true);
    }

    /**
     * Whether a printing toggle can do anything, saying why if not.
     *
     * These reach HOL by sending it an assignment, so they still need
     * a notebook session; nothing connects them to the language
     * server yet.  `isActive` would say "No active HOL session", which
     * reads as though the user forgot to start something, when in the
     * server's world there is nothing to start.
     */
    private printingToggleAvailable(): boolean {
        this.sync();
        if (this.notebook?.kernel.running) {
            return true;
        }

        vscode.window.showErrorMessage(
            'Printing toggles are not connected to the HOL language ' +
            'server yet; they only take effect in a notebook session.');
        error('printing toggle: no notebook session, and no LSP route');
        return false;
    }

    /* The IDE providers used to live here, fed by the symbol
     * indexer.  They belong to the language server now: it advertises
     * hover, definition, documentSymbol, workspaceSymbol and
     * completion, and vscode-languageclient registers them from those
     * capabilities.  One implementation, and it is the one with HOL
     * loaded.
     */
};

