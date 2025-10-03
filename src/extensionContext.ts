import * as vscode from 'vscode';
import * as path from 'path';
import { log, error, EXTENSION_ID, KERNEL_ID } from './common';
import { HolNotebook } from './notebook';
import { HOLIDE, entryToCompletionItem, entryToSymbol, isAccessibleEntry } from './holIDE';
import { ExecutionTracker, ActionType } from './executionTracker';

/**
 * Generate a HOL lexer location pragma from a vscode Position value.
 */
function positionToLocationPragma(pos: vscode.Position): string {
    return `(*#loc ${pos.line + 1} ${pos.character} *)`;
}

/**
 * Get the editors current selection if any, or the contents of the editor's
 * current line otherwise.
 */
function getSelection(editor: vscode.TextEditor): vscode.Selection {
    const selection = editor.selection;
    return selection.isEmpty 
            ? new vscode.Selection(selection.active.line, 0, selection.active.line, editor.document.lineAt(selection.active.line).text.length)
            : selection;
}

/**
 * Adds a location pragma to the text at the given position.
 */
function addLocationPragma(text: string, position: vscode.Position) {
    const locPragma = positionToLocationPragma(position);
    const trace = '"show_typecheck_errors"';
    const data =
        `let val old = Feedback.current_trace ${trace}\n` +
        `    val _ = Feedback.set_trace ${trace} 0\n` +
        `in (${locPragma}) before Feedback.set_trace ${trace} old end;\n` +
        text;
    return data;
}

// /**
//  * Preprocess any `open` declarations in a string. Any declarations are sorted,
//  * and for each declaration a `load`-call is generated. If there are no `open`s
//  * in the text, then this does nothing.
//  */
// function processOpens(text: string): string {
//     text = removeComments(text).replace(/\n\s*\n/g, '\n').replace(/\r/g, '');
//     let index = 0;
//     let buffer = [];
//     let quiet = false;
//     function setQuiet(q: boolean) {
//         if (quiet != q) {
//             buffer.push('\nval _ = HOL_Interactive.toggle_quietdec();\n');
//         }
//         quiet = q;
//     }
//     const theoriesSet = new Set<string>();
//     getImports(text, s => theoriesSet.add(s), (start, end) => {
//         const mid = text.substring(index, start);
//         if (/[^\s;]/.test(mid)) setQuiet(false);
//         buffer.push(mid);
//         setQuiet(true);
//         buffer.push(text.substring(start, end));
//         index = end;
//     });
//     if (!theoriesSet.size) return text;
//     const theories: string[] = [];
//     theoriesSet.forEach(s => theories.push(s));
//
//     setQuiet(false);
//     const banner = `val _ = print "Loading: ${theories.join(' ')} ...\\n";`;
//     const loads = theories.map((s) => `val _ = load "${s}";\n`);
//     const bannerDone = 'val _ = print "Done loading theories.\\n"\n';
//     buffer.unshift(banner, ...loads);
//     buffer.push(bannerDone, text.substring(index));
//     return buffer.join('');
// }

/**
 * Preprocess a tactic selection by removing leading tacticals and trailing
 * tacticals (plus possibly an opening parenthesis).
 */
function processTactics(text: string): string {
    const tacticalBegin = /^(\\\\|>>|>-|\bTHEN[1]?\b)(\s)/;
    const tacticalEnd = /(\\\\|>>|>-|\bTHEN[1]?\b)(\s*)[\(]?$/;
    return text.trim().replace(tacticalBegin, '$2').replace(tacticalEnd, '$2');
}

/**
 * Select a chunk of text delimited by `init` and `stop` in the editor `editor`.
 */
function selectBetween(editor: vscode.TextEditor, init: RegExp, stop: RegExp): vscode.Selection | undefined {
    const selection = editor.selection;
    const document = editor.document;
    const currentLine = selection.active.line;

    let startLine, startCol;

    for (let i = currentLine; i >= 0; i--) {
        const text = document.lineAt(i).text;
        const match = init.exec(text);
        if (match) {
            startLine = i;
            startCol = match.index + match[0].length;
            break;
        }
    }

    if (startLine === undefined || startCol === undefined) {
        return;
    }

    let endLine, endCol;

    for (let i = currentLine; i < document.lineCount; i++) {
        let text = document.lineAt(i).text;
        let offset = 0;

        // If we're at the same line as the starting match, and if the `init`
        // and `stop` regexes both match the same token, then we need to skip
        // the init token, or we'll produce an empty range.
        if (i === startLine) {
            text = text.slice(startCol);
            offset += startCol;
        }

        const match = stop.exec(text);
        if (match) {
            endLine = i;
            endCol = match.index + offset;
            break;
        }
    }

    if (endLine === undefined || endCol === undefined) {
        return;
    }

    return new vscode.Selection(startLine, startCol, endLine, endCol);
};

/**
 * Attempt to extract a goal from the current editor. Start by searching
 * forwards and backwards for a matching `{Theorem,Triviality}:-Proof` pair.
 * If this does not work, search for the nearest pair of double term quotes. If
 * this does not work, search for the nearest pair of single term quotes.
 * Otherwise, return nothing.
 *
 * If you're between two goals or terms you will select a large chunk of
 * everything.
 *
 * @note this function embeds a location pragma in the string it returns.
 */
function extractGoal(editor: vscode.TextEditor): [string, vscode.Selection] | undefined {
    const selection = editor.selection;
    const document = editor.document;

    if (!selection.isEmpty) {
        const locPragma = positionToLocationPragma(selection.anchor);
        return [locPragma, selection];
    }

    const spanBegin = /^(Theorem|Triviality)\s+[^\[\:]+(\[[^\]]*\])?\s*\:/;
    const spanEnd = /^Proof/;

    let sel;
    if ((sel = selectBetween(editor, spanBegin, spanEnd)) ||
        (sel = selectBetween(editor, /“/, /”/)) ||
        (sel = selectBetween(editor, /‘/, /’/)) ||
        (sel = selectBetween(editor, /``/, /``/)) ||
        (sel = selectBetween(editor, /`/, /`/))) {
        const locPragma = positionToLocationPragma(sel.anchor);
        return [locPragma, sel];
    }

    return;
}

/**
 * Identical to {@link extractGoal} but only accepts term quotations.
 * @todo Merge with extractGoal.
 */
function extractSubgoal(editor: vscode.TextEditor): [string, vscode.Selection] | undefined {
    const selection = editor.selection;
    const document = editor.document;

    if (!selection.isEmpty) {
        const locPragma = positionToLocationPragma(selection.anchor);
        return [locPragma, selection];
    }

    let sel;
    if ((sel = selectBetween(editor, /‘/, /’/)) ||
        (sel = selectBetween(editor, /`/, /`/))) {
        const locPragma = positionToLocationPragma(sel.anchor);
        return [locPragma, sel];
    }

    return;
}

export class HOLExtensionContext implements
    vscode.DefinitionProvider, vscode.HoverProvider, vscode.DocumentSymbolProvider,
    vscode.WorkspaceSymbolProvider, vscode.CompletionItemProvider {

    /** Currently active notebook editor (if any). */
    public notebook?: HolNotebook;

    /** Execution tracker for managing code decorations and history. */
    public executionTracker: ExecutionTracker;

    constructor(
        private context: vscode.ExtensionContext,

        /** Path to the HOL installation to use. */
        public holPath: string,

        /** Current IDE class instance. */
        public holIDE?: HOLIDE
    ) {
        this.executionTracker = new ExecutionTracker();
    }

    private pendingActionCell: Map<string, string> = new Map(); // cellUri -> actionId
    
    private setupKernelListeners() {
        if (this.notebook?.kernel) {
            this.notebook.kernel.onExecComplete(({ cell, success }) => {
                this.handleExecutionComplete(cell, success);
            });
        }
    }

    private handleExecutionComplete(cell: vscode.NotebookCell, success: boolean) {
        const cellKey = `${cell.notebook.uri.toString()}#${cell.index}`;
        const actionId = this.pendingActionCell.get(cellKey);
        if (actionId) {
            this.pendingActionCell.delete(cellKey);
            if (success) {
                this.executionTracker.confirmAction(actionId);
            } else {
                this.executionTracker.cancelAction(actionId);
            }
        }
    }

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
                    e.notebook.cellCount === 0 &&
                    e.notebook.notebookType === 'interactive'
                );
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

        this.setupKernelListeners();

        log('Started session');
    }

    /**
     * Stop the HOL terminal session.
     */
    stopSession() {
        if (!this.isActive()) {
            return;
        }

        this.executionTracker.clearAll();

        log('Stopped session');
        this.notebook!.close();
    }

    /**
     * Restart the HOL terminal session.
     */
    restartSession(editor: vscode.TextEditor) {
        this.executionTracker.clearAll();

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

        const selection = getSelection(editor);
        const text = editor.document.getText(selection);

        const actionId = this.executionTracker.recordPendingAction(ActionType.selection, editor, selection, text);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);

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
        
        const actionId = this.executionTracker.recordPendingAction(ActionType.untilCursor, editor, selection, text);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);

        await this.notebook!.send(text, true, true);
    }

    /**
     * Send a goal selection to the terminal.
     */
    async sendGoal(editor: vscode.TextEditor) {
        this.sync();
        if (!this.notebook?.kernel.running) {
            await this.startSession(editor);
        }

        const goalData = extractGoal(editor);
        if (!goalData) {
            vscode.window.showErrorMessage('Unable to select a goal term');
            error('Unable to select goal term');
            return;
        }
        let [locPragma, goalSelection] = goalData;
        const text = editor.document.getText(goalSelection);
        
        const faketext = `proofManagerLib.g(\`${text}\`)`;
        const realtext = `proofManagerLib.g(\`${locPragma}${text}\`)`;
        const full = `let val x = ${realtext}; val _ = proofManagerLib.set_backup 100 in x end`;
        
        const actionId = this.executionTracker.recordPendingAction(ActionType.goal, editor, goalSelection, text);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);

        await this.notebook!.send(faketext, false, true, full);
    }

    /**
     * Select a term quotation and set it up as a subgoal.
     */
    async sendSubgoal(editor: vscode.TextEditor) {
        if (!this.isActive()) {
            return;
        }

        let subGoalData = extractSubgoal(editor);
        if (!subGoalData) {
            vscode.window.showErrorMessage('Unable to select a subgoal term');
            error('Unable to select subgoal term');
            return;
        }
        const [locPragma, subGoalSelection] = subGoalData;
        const text = editor.document.getText(subGoalSelection);

        const faketext = `proofManagerLib.e(sg\`${text}\`)`;
        const realtext = `proofManagerLib.e(sg\`${locPragma}${text}\`)`;
        
        const actionId = this.executionTracker.recordPendingAction(ActionType.subgoal, editor, subGoalSelection, text);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);
        
        await this.notebook!.send(faketext, false, true, realtext);
    }

    /**
     * Send a tactic to the terminal.
     */
    async sendTactic(editor: vscode.TextEditor) {
        if (!this.isActive()) {
            return;
        }

        const tacticSelection = getSelection(editor);
        const tacticText0 = editor.document.getText(tacticSelection);
        const tacticText = processTactics(tacticText0);
        const text = `proofManagerLib.e(${tacticText})`;
        const full = addLocationPragma(text, editor.selection.start);

        const actionId = this.executionTracker.recordPendingAction(ActionType.tactic, editor, tacticSelection, tacticText);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);

        await this.notebook!.send(text, false, true, full);
    }


    /**
     * Send a tactic line to the terminal.
     */
    async sendTacticLine(editor: vscode.TextEditor) {
        if (!this.isActive()) {
            return;
        }

        const currentLine = editor.selection.active.line;
        const tacticText0 = editor.document.lineAt(currentLine).text;
        const tacticText = processTactics(tacticText0);
        const text = `proofManagerLib.e(${tacticText})`;
        const full = addLocationPragma(text, editor.selection.start);

        const tacticSelection = new vscode.Range(currentLine, 0, currentLine, editor.document.lineAt(currentLine).text.length);
        const actionId = this.executionTracker.recordPendingAction(ActionType.tacticLine, editor, tacticSelection, tacticText);
        const cellIndex = this.notebook!.notebookEditor.notebook.cellCount;
        const cellKey = `${this.notebook!.notebookEditor.notebook.uri.toString()}#${cellIndex}`;
        this.pendingActionCell.set(cellKey, actionId);

        await this.notebook!.send(text, false, true, full);
    }

    /**
     * Show current goal.
     */
    async showCurrentGoal() {
        if (!this.isActive()) {
            return;
        }

        await this.notebook!.send('proofManagerLib.p ()', false, true);
    }


    /**
     * Rotate goal.
     */
    async rotateGoal() {
        if (!this.isActive()) {
            return;
        }

        await this.notebook!.send('proofManagerLib.rotate 1', false, true);
    }

    /**
     * Step backwards goal.
     */
    async stepbackGoal() {
        if (!this.isActive()) {
            return;
        }

        this.executionTracker.stepBack(1);

        await this.notebook!.send('proofManagerLib.backup ()', false, true);
    }

    /**
     * Restart goal.
     */
    async restartGoal() {
        if (!this.isActive()) {
            return;
        }

        this.executionTracker.clearCurrentGoal();

        await this.notebook!.send('proofManagerLib.restart ()', false, true);
    }

    /**
     * Drop goal.
     */
    async dropGoal() {
        if (!this.isActive()) {
            return;
        }

        this.executionTracker.dropCurrentGoal();

        await this.notebook!.send('proofManagerLib.drop ()', false, true);
    }

    /**
     * Toggle printing of terms with or without types.
     */
    async toggleShowTypes() {
        if (!this.isActive()) {
            return;
        }

        await this.notebook!.send('Globals.show_types := not (!Globals.show_types)', false, true);
    }

    /**
     * Toggle printing of theorem hypotheses.
     */
    async toggleShowAssums() {
        if (!this.isActive()) {
            return;
        }
        await this.notebook!.send('Globals.show_assums := not (!Globals.show_assums)', false, true);
    }

    /**
     * Clear all execution decorations and history.
     */
    clearExecutionHistory() {
        this.executionTracker.clearAll();
        vscode.window.showInformationMessage('Execution history cleared');
    }

    /**
     * Remove the last executed action (useful for failed tactics).
     */
    removeLastAction() {
        const removed = this.executionTracker.stepBack(1);
        if (removed.length > 0) {
            vscode.window.showInformationMessage(`Removed last action: ${removed[0].type}`);
        } else {
            vscode.window.showInformationMessage('No actions to remove');
        }
    }

    /**
     * See {@link vscode.HoverProvider}.
     */
    async provideHover(document: vscode.TextDocument, position: vscode.Position, _token: vscode.CancellationToken) {
        const results: vscode.MarkdownString[] = [];
        const sels = vscode.window.activeTextEditor?.selections;
        let inRange = new vscode.Range(position, position);
        if (sels) {
            for (const sel of sels) {
                if (sel.contains(position)) {
                    inRange = sel;
                    break;
                }
            }
        }
        const promise = this.holIDE?.getHoverInfo(document, inRange, results);
        const wordRange = document.getWordRangeAtPosition(position);
        const word = document.getText(wordRange);
        const entry = this.holIDE?.findEntry(entry =>
            entry.name === word &&
            isAccessibleEntry(entry, this.holIDE!.imports[document.uri.toString()], document));
        const range = await promise?.catch();
        if (entry) {
            const markdownString = new vscode.MarkdownString();
            markdownString.appendMarkdown(`**${entry.type}:** ${entry.name}\n\n`);
            markdownString.appendCodeblock(entry.statement);
            results.push(markdownString);
        }
        if (results) {
            return new vscode.Hover(results, range ?? wordRange);
        }
    }

    /**
     * See {@link vscode.DefinitionProvider}.
     */
    async provideDefinition(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken,
    ): Promise<vscode.DefinitionLink[]> {
        const promise = this.holIDE?.gotoDefinition(document, position);
        const wordRange = document.getWordRangeAtPosition(position);
        const word = document.getText(wordRange);
        const entry = this.holIDE?.findEntry(entry =>
            entry.name === word &&
            isAccessibleEntry(entry, this.holIDE!.imports[document.uri.toString()], document));
        const defns: vscode.DefinitionLink[] = (await promise?.catch()) ?? [];
        if (defns.length === 0 && entry) {
            const position = new vscode.Position(entry.line - 1, 0);
            defns.push({
                targetUri: vscode.Uri.file(entry.file),
                targetRange: new vscode.Range(position, position)
            });
        }
        return defns;
    }

    /**
     * See {@link vscode.DocumentSymbolProvider}.
     */
    provideDocumentSymbols(
        document: vscode.TextDocument,
        _token: vscode.CancellationToken,
    ) {
        return this.holIDE?.documentEntries(document).map(entryToSymbol);
    }

    /**
     * See {@link vscode.WorkspaceSymbolProvider<T>}.
     */
    provideWorkspaceSymbols(
        query: string,
        _token: vscode.CancellationToken,
    ) {
        const symbols: vscode.SymbolInformation[] = [];
        const matcher = new RegExp(query, "i" /* ignoreCase */);
        this.holIDE?.forEachEntry(entry => {
            if (matcher.test(entry.name)) {
                symbols.push(entryToSymbol(entry));
            }
        });
        return symbols;
    }

    /**
     * See {@link vscode.CompletionItemProvider}.
     */
    provideCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken,
        _context: vscode.CompletionContext,
    ) {
        const wordRange = document.getWordRangeAtPosition(position);
        if (!wordRange) {
            return [];
        }

        const word = document.getText(wordRange);
        const completions: vscode.CompletionItem[] = [];
        const matcher = new RegExp(word, "i" /* ignoreCase */);
        this.holIDE?.forEachEntry(entry => {
            if (matcher.test(entry.name) &&
                isAccessibleEntry(entry, this.holIDE!.imports[document.uri.toString()], document)) {
                completions.push(entryToCompletionItem(entry));
            }
        });
        return completions;
    }
};

