import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { HOLIDE } from './holIDE';
import { HOLExtensionContext } from './extensionContext';
import { log, error, holdir } from './common';


function loadUnicodeCompletions(context: vscode.ExtensionContext): { [key: string]: string } {
    let unicodeCompletionsFilepath = context.asAbsolutePath('unicode-completions.json');

    log('Loading unicode completions.');
    let completions: { [key: string]: string } = {};
    try {
        const data = fs.readFileSync(unicodeCompletionsFilepath);
        completions = JSON.parse(data.toString());
    } catch (err) {
        error(`Unable to read unicode completions file: ${err}`);
        vscode.window.showErrorMessage('Unable to load unicode completions.');
    }
    return completions;
}

let hol4selector: vscode.DocumentSelector = {
    scheme: 'file',
    language: 'hol4'
};

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

    let holIDE: HOLIDE | undefined;
    if (vscode.workspace.getConfiguration('hol4-mode').get('indexing')
        && vscode.workspace.workspaceFolders?.length) {
        // Get the path to the current workspace root. This class is constructed
        // by the extension, which is activated by opening a HOL4 document. By
        // this time there should be a workspace.
        if (vscode.workspace.workspaceFolders.length == 1) {
            const workspacePath = vscode.workspace.workspaceFolders[0].uri.fsPath;
            holIDE = new HOLIDE(context, holPath, workspacePath);
        } else {
            vscode.window.showErrorMessage('HOL4 mode: multi-root workspaces not supported');
            error('workspace has too many roots');
        }
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
    return new HOLExtensionContext(context, holPath, holIDE);
}

let holExtensionContext: HOLExtensionContext | undefined;
export function activate(context: vscode.ExtensionContext) {
    holExtensionContext = initialize(context);
    if (!holExtensionContext) {
        error("Unable to initialize extension.");
        return;
    }

    let completions = loadUnicodeCompletions(context);

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

        // Send a goal selection to the terminal.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendGoal', (editor) => {
            holExtensionContext?.sendGoal(editor);
        }),

        // Select a term quotation and set it up as a subgoal.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendSubgoal', (editor) => {
            holExtensionContext?.sendSubgoal(editor);
        }),

        // Send a tactic selection to the terminal.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendTactic', (editor) => {
            holExtensionContext?.sendTactic(editor);
        }),

        // Send a tactic line to the terminal.
        vscode.commands.registerTextEditorCommand('hol4-mode.sendTacticLine', (editor) => {
            holExtensionContext?.sendTacticLine(editor);
        }),

        // Show goal.
        vscode.commands.registerCommand('hol4-mode.proofmanShow', () => {
            holExtensionContext?.showCurrentGoal();
        }),

        // Rotate goal.
        vscode.commands.registerCommand('hol4-mode.proofmanRotate', () => {
            holExtensionContext?.rotateGoal();
        }),

        // Step backwards goal.
        vscode.commands.registerCommand('hol4-mode.proofmanBack', () => {
            holExtensionContext?.stepbackGoal();
        }),

        // Restart goal.
        vscode.commands.registerCommand('hol4-mode.proofmanRestart', () => {
            holExtensionContext?.restartGoal();
        }),

        // Drop goal.
        vscode.commands.registerCommand('hol4-mode.proofmanDrop', () => {
            holExtensionContext?.dropGoal();
        }),

        // Toggle printing of terms with or without types
        vscode.commands.registerCommand('hol4-mode.toggleShowTypes', () => {
            holExtensionContext?.toggleShowTypes();
        }),

        // Toggle printing of theorem assumptions
        vscode.commands.registerCommand('hol4-mode.toggleShowAssums', () => {
            holExtensionContext?.toggleShowAssums();
        }),

        // Run Holmake in current directory
        vscode.commands.registerTextEditorCommand('hol4-mode.holmake', editor => {
            const docPath = path.dirname(editor.document.uri.fsPath);
            const terminal = vscode.window.createTerminal({
                cwd: docPath,
                name: 'Holmake',
                shellPath: 'Holmake',
                message: `Running Holmake in directory: ${docPath} ...`
            });
            terminal.show(true);
        }),

        vscode.commands.registerCommand('hol4-mode.clearAll', async () => {
            await holExtensionContext?.notebook?.clearAll();
        }),

        vscode.commands.registerCommand('hol4-mode.restart', () => {
            (async () => {
                await holExtensionContext?.notebook?.stop();
                await holExtensionContext?.notebook?.start();
            })();
            holExtensionContext?.holIDE?.restartServers();
        }),

        vscode.commands.registerCommand('hol4-mode.collapseAllCells', async () => {
            await holExtensionContext?.notebook?.collapseAll();
        }),

        vscode.commands.registerCommand('hol4-mode.expandAllCells', async () => {
            await holExtensionContext?.notebook?.expandAll();
        }),

        // Refresh the import list for the currently active document.
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (editor) {
                const doc = editor.document;
                if (doc.languageId == 'hol4' && doc.uri.scheme == 'file') {
                    (async () => {
                        const server = await holExtensionContext?.holIDE?.startServer(doc);
                        if (server) await holExtensionContext?.holIDE?.compileDocument(server, doc);
                    })();
                    holExtensionContext?.holIDE?.updateImports(doc);
                }
            }
        }),

        vscode.workspace.onDidSaveTextDocument(doc => {
            if (doc.languageId == 'hol4' && doc.uri.scheme == 'file') {
                (async () => {
                    const server = await holExtensionContext?.holIDE?.startServer(doc);
                    if (server) await holExtensionContext?.holIDE?.compileDocument(server, doc);
                })();
                holExtensionContext?.holIDE?.indexDocument(doc);
            }
        }),

        vscode.commands.registerCommand('hol4-mode.indexWorkspace', () => {
            holExtensionContext?.holIDE?.indexWorkspace();
        }),

        vscode.commands.registerCommand('hol4-mode.refreshIndex', () => {
            holExtensionContext?.holIDE?.refreshIndex();
        }),

        vscode.languages.registerHoverProvider(
            hol4selector,
            holExtensionContext,
        ),

        vscode.languages.registerDefinitionProvider(
            hol4selector,
            holExtensionContext,
        ),

        vscode.languages.registerDocumentSymbolProvider(
            hol4selector,
            holExtensionContext,
        ),

        vscode.languages.registerWorkspaceSymbolProvider(
            holExtensionContext,
        ),

        // HOL IDE commands END

        vscode.languages.registerCompletionItemProvider(hol4selector,
            {
                async provideCompletionItems(_document, position, _token, context) {
                    let items = [];
                    let range = new vscode.Range(position.translate(0, -1), position);
                    for (const matchKey in completions) {
                        let matchVal = completions[matchKey];
                        let item = new vscode.CompletionItem(context.triggerCharacter + matchKey);
                        item.kind = vscode.CompletionItemKind.Text;
                        item.range = range;
                        item.detail = matchVal;
                        item.insertText = matchVal;
                        items.push(item);
                    }
                    return items;
                }
            },
            ...['\\']
        ),

        vscode.languages.registerCompletionItemProvider(
            hol4selector,
            holExtensionContext,
        ),
    ];

    commands.forEach((cmd) => context.subscriptions.push(cmd));
}

// this method is called when your extension is deactivated
export function deactivate() {
    holExtensionContext?.stopSession()
}
