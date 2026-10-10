import * as vscode from 'vscode';
import { HOLExtensionContext } from './extensionContext';
import { error, holdir } from './common';
import { AbbreviationFeature } from './abbreviations';
import { smartQuote } from './holInput';
import { classifyOffset } from './holContext';
import { LspClients } from './lspClient';
import { GoalsView } from './goalsView';
import { Holmake } from './holmake';


/**
 * Initialize the HOL extension.
 *
 * @returns An extension context if successful, or `undefined` otherwise.
 */
function initialize(context: vscode.ExtensionContext): HOLExtensionContext | undefined {
    let holPath = holdir();
    if (!holPath) {
        holPath = process.env['HOLDIR'];
        if (holPath === undefined) {
            vscode.window.showErrorMessage('HOL4 mode: HOLDIR environment variable not set');
            error('Unable to read HOLDIR environment variable, exiting');
            return;
        }
    } else if (holPath.startsWith('$')) {
        holPath = process.env[holPath.slice(1)] ?? holPath;
    }

    // Cleanup orphaned tabs from previous session
    for (const group of vscode.window.tabGroups.all) {
        for (const tab of group.tabs) {
            if (tab.label == 'HOL4 Session' &&
                !vscode.workspace.notebookDocuments.some(doc => doc.uri == (tab.input as { uri?: vscode.Uri }).uri)) {
                vscode.window.tabGroups.close(tab);
            }
        }
    }
    return new HOLExtensionContext(context, holPath);
}

let holExtensionContext: HOLExtensionContext | undefined;
let lspClients: LspClients | undefined;
let goalsView: GoalsView | undefined;
let holmake: Holmake | undefined;
export function activate(context: vscode.ExtensionContext) {
    holExtensionContext = initialize(context);
    if (!holExtensionContext) {
        error("Unable to initialize extension.");
        return;
    }

    // One per window: the exit-code listener it registers has to be
    // registered once, not once per run.
    holmake = new Holmake(() => holExtensionContext?.holPath);
    context.subscriptions.push(holmake);

    const lspEnabled = vscode.workspace.getConfiguration('hol4-mode')
        .get<boolean>('lsp.enabled', true);
    if (lspEnabled) {
        lspClients = new LspClients(holExtensionContext.holPath);
        lspClients.start();
        context.subscriptions.push(lspClients);
        goalsView = new GoalsView(lspClients);
        context.subscriptions.push(goalsView);
        // The extension activates on `onLanguage:hol4', so there is a
        // HOL buffer by now and the pane has something to be about.
        // `preserveFocus' is set where the panel is created, so this
        // does not take the cursor out of the editor.
        if (vscode.workspace.getConfiguration('hol4-mode')
                .get<boolean>('lsp.openGoalsOnStartup', true)) {
            goalsView.show();
        }
    }

    let commands = [
        // Start a new HOL4 session.
        // Opens up a terminal and starts HOL4.
        vscode.commands.registerTextEditorCommand('hol4-mode.startSession', (editor) => {
            holExtensionContext?.startSession(editor);
        }),

        // Stop the current session, if any.
        vscode.commands.registerCommand('hol4-mode.stopSession', () => {
            holExtensionContext?.stopSession();
        }),

        // Interrupt the current session, if any.
        vscode.commands.registerCommand('hol4-mode.interrupt', () => {
            holExtensionContext?.interrupt();
        }),

        // Send selection to the terminal; preprocess to find `open` and `load`
        // calls.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendSelection', (editor) => {
            holExtensionContext?.sendSelection(editor);
        }),

        // Send all text up to and including the current line in the current editor
        // to the terminal.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendUntilCursor', (editor) => {
            holExtensionContext?.sendUntilCursor(editor);
        }),

        // Toggle printing of terms with or without types
        vscode.commands.registerCommand('hol4-mode.toggleShowTypes', () => {
            holExtensionContext?.toggleShowTypes();
        }),

        // Toggle printing of theorem assumptions
        vscode.commands.registerCommand('hol4-mode.toggleShowAssums', () => {
            holExtensionContext?.toggleShowAssums();
        }),

        // Run Holmake in the directory of the current document.
        //
        // A task rather than a terminal.  This used to be a terminal
        // with `shellPath: 'Holmake'`, which made Holmake the
        // terminal's root process -- and VS Code closes a terminal
        // when its root process exits.  The output scrolled past and
        // the panel vanished, so a failed build, a clean one, and a
        // Holmake that was never installed all looked alike.  See
        // src/holmake.ts.
        vscode.commands.registerTextEditorCommand('hol4-mode.holmake',
            (editor) => {
                void holmake?.run(editor.document);
            }),

        vscode.commands.registerCommand('hol4-mode.clearAll', async () => {
            await holExtensionContext?.notebook?.clearAll();
        }),

        vscode.commands.registerCommand('hol4-mode.restart', () => {
            (async () => {
                await holExtensionContext?.notebook?.stop();
                await holExtensionContext?.notebook?.start();
            })();
        }),

        vscode.commands.registerCommand('hol4-mode.collapseAllCells', async () => {
            await holExtensionContext?.notebook?.collapseAll();
        }),

        vscode.commands.registerCommand('hol4-mode.expandAllCells', async () => {
            await holExtensionContext?.notebook?.expandAll();
        }),

        vscode.commands.registerCommand('hol4-mode.lsp.toggleGoalsPane', () => {
            goalsView?.toggle();
        }),

        vscode.commands.registerCommand('hol4-mode.lsp.restart', () => {
            lspClients?.restartActive();
        }),

        vscode.commands.registerCommand('hol4-mode.lsp.showOutput', () => {
            lspClients?.showOutput();
        }),

        vscode.commands.registerCommand('hol4-mode.lsp.retryCompile', () => {
            lspClients?.retryCompileActive();
        }),

        vscode.commands.registerCommand(
            'hol4-mode.lsp.gotoOutstandingProof', () => {
                lspClients?.gotoOutstandingProof();
            }),

        vscode.commands.registerCommand('hol4-mode.lsp.search', () => {
            lspClients?.searchTheorems();
        }),

        // Text-editor commands: what they evaluate and where they
        // evaluate it both come from the editor, so they need one
        // rather than looking it up.  `evalSelection` falls through to
        // `evalPrompt` when there is nothing selected; `evalPrompt` is
        // registered as well so the box has a name in the palette.
        vscode.commands.registerTextEditorCommand(
            'hol4-mode.lsp.evalSelection', (editor) => {
                void lspClients?.evalSelection(editor);
            }),

        vscode.commands.registerTextEditorCommand(
            'hol4-mode.lsp.evalPrompt', (editor) => {
                void lspClients?.evalPrompt(editor);
            }),

        vscode.commands.registerCommand('hol4-mode.lsp.showEvalOutput', () => {
            lspClients?.showEvalOutput();
        }),

        // The backtick key.  HOL writes terms as `‘…’` and types as
        // `“…”`, and neither is on a keyboard; Emacs binds this key to
        // `holscript-dbl-backquote` for the same reason.  It is a
        // command rather than a change listener because three of the
        // four things it does -- stepping over a closing delimiter,
        // retyping an existing quotation, wrapping a selection -- are
        // not insertions, and a listener only runs once the character is
        // already in the buffer.
        vscode.commands.registerTextEditorCommand(
            'hol4-mode.input.smartQuote', (editor) => {
                void insertSmartQuote(editor);
            }),

        // No language providers are registered here.  Hover,
        // definition, documentSymbol, workspaceSymbol and completion
        // all come from the language server, which
        // vscode-languageclient wires up from the capabilities it
        // advertises.  Registering our own would be a second answer to
        // the same question.
        new AbbreviationFeature(),
    ];

    commands.forEach((cmd) => context.subscriptions.push(cmd));
}

async function insertSmartQuote(editor: vscode.TextEditor) {
    // Hand the keystroke back to the editor's own type handler, so a
    // literal backtick still auto-closes and still passes through any
    // other extension that owns `type`.
    const typeBacktick = () =>
        vscode.commands.executeCommand('type', { text: '`' });

    if (!vscode.workspace.getConfiguration('hol4-mode')
            .get<boolean>('input.smartQuotes', true)) {
        await typeBacktick();
        return;
    }

    const doc = editor.document;
    const text = doc.getText();
    const start = doc.offsetAt(editor.selection.start);
    const end = doc.offsetAt(editor.selection.end);
    const action = smartQuote(text, start, end, (o) => classifyOffset(text, o));

    if (action.kind === 'literal') {
        await typeBacktick();
        return;
    }
    if (action.kind === 'move') {
        const p = doc.positionAt(action.to);
        editor.selection = new vscode.Selection(p, p);
        return;
    }
    const ok = await editor.edit((builder) => {
        for (const e of action.edits) {
            builder.replace(
                new vscode.Range(doc.positionAt(e.offset),
                                 doc.positionAt(e.offset + e.length)),
                e.newText);
        }
    });
    if (ok) {
        const p = doc.positionAt(action.cursor);
        editor.selection = new vscode.Selection(p, p);
    }
}

// this method is called when your extension is deactivated
export function deactivate() {
    holExtensionContext?.stopSession()
}
