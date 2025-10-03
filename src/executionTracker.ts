import * as vscode from 'vscode';

export enum ActionType {
    goal = 'goal',
    selection = 'selection',
    untilCursor = 'untilcursor',
    subgoal = 'subgoal',
    tactic = 'tactic',
    tacticLine = 'tacticline'
}

export interface ExecutedAction {
    id: string;
    type: ActionType;
    documentUri: string;
    range: vscode.Range;
    text: string;
}

export interface PendingAction {
    type: ActionType;
    editor: vscode.TextEditor;
    range: vscode.Range;
    text: string;
}

/**
 * Manages tracking and visual decoration of executed code ranges
 */
export class ExecutionTracker {
    private executedActions: ExecutedAction[] = [];
    private executedDecorationType: vscode.TextEditorDecorationType;
    private pendingDecorationType: vscode.TextEditorDecorationType;
    private nextActionId = 1;
    private currentGoalId: string | null = null;
    private pendingActions: Map<string, PendingAction> = new Map();

    private isExecutionTrackingEnabled(): boolean {
        return vscode.workspace.getConfiguration('hol4-mode').get('executionTracking', false);
    }

    constructor() {
        this.executedDecorationType = vscode.window.createTextEditorDecorationType({
            backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
            isWholeLine: false,
            overviewRulerColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
            overviewRulerLane: vscode.OverviewRulerLane.Right
        });

        this.pendingDecorationType = vscode.window.createTextEditorDecorationType({
            backgroundColor: 'rgba(255, 255, 255, 0.1)',
            border: '1px dashed',
            borderColor: 'rgba(255, 255, 255, 0.3)',
            isWholeLine: false,
            overviewRulerColor: 'rgba(255, 255, 255, 0.2)',
            overviewRulerLane: vscode.OverviewRulerLane.Right
        });

        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (editor) {
                this.updateDecorations(editor);
            }
        });

        vscode.window.onDidChangeVisibleTextEditors(editors => {
            editors.forEach(editor => {
                this.updateDecorations(editor);
            });
        });

        if (this.isExecutionTrackingEnabled()) {
            vscode.window.visibleTextEditors.forEach(editor => {
                this.updateDecorations(editor);
            });
        }
    }

    recordAction(
        type: ActionType,
        editor: vscode.TextEditor,
        range: vscode.Range,
        text: string,
    ): string {
        const action: ExecutedAction = {
            id: `action-${this.nextActionId++}`,
            type,
            documentUri: editor.document.uri.toString(),
            range,
            text,
        };

        this.executedActions.push(action);
        this.updateDecorations(editor);
        
        if (type === ActionType.goal) {
            this.currentGoalId = action.id;
        }
        
        return action.id;
    }

    recordPendingAction(
        type: ActionType,
        editor: vscode.TextEditor,
        range: vscode.Range,
        text: string,
    ): string {
        const actionId = `action-${this.nextActionId++}`;
        this.pendingActions.set(actionId, {
            type,
            editor,
            range,
            text,
        });
        
        this.updateDecorations(editor);
        
        return actionId;
    }

    confirmAction(actionId: string): void {
        const pending = this.pendingActions.get(actionId);
        if (pending) {
            this.pendingActions.delete(actionId);
            this.recordAction(
                pending.type,
                pending.editor,
                pending.range,
                pending.text,
            );
            this.updateDecorations(pending.editor);
        }
    }

    cancelAction(actionId: string): void {
        const pending = this.pendingActions.get(actionId);
        if (pending) {
            this.pendingActions.delete(actionId);
            this.updateDecorations(pending.editor);
        }
    }

    getActionsForDocument(documentUri: string): ExecutedAction[] {
        return this.executedActions.filter(action => action.documentUri === documentUri);
    }

    stepBack(count: number = 1): ExecutedAction[] {
        const removedActions: ExecutedAction[] = [];
        for (let i = 0; i < count && this.executedActions.length > 0 && this.currentGoalId && this.executedActions[this.executedActions.length - 1].id !== this.currentGoalId; i++) {
            const removed = this.executedActions.pop();
            if (removed) {
                removedActions.push(removed);
            }
        }

        vscode.window.visibleTextEditors.forEach(editor => {
            this.updateDecorations(editor);
        });

        return removedActions;
    }

    clearAll(): ExecutedAction[] {
        const clearedActions = [...this.executedActions];
        this.executedActions = [];
        this.currentGoalId = null;

        vscode.window.visibleTextEditors.forEach(editor => {
            this.updateDecorations(editor);
        });

        return clearedActions;
    }

    clearCurrentGoal(): ExecutedAction[] {
        if (!this.currentGoalId) {
            return [];
        }

        const goalIndex = this.executedActions.findIndex(action => action.id === this.currentGoalId);
        if (goalIndex === -1) {
            return [];
        }

        const removedActions = this.executedActions.splice(goalIndex + 1);

        vscode.window.visibleTextEditors.forEach(editor => {
            this.updateDecorations(editor);
        });

        return removedActions;
    }

    dropCurrentGoal(): ExecutedAction[] {
        if (!this.currentGoalId) {
            return [];
        }

        const goalIndex = this.executedActions.findIndex(action => action.id === this.currentGoalId);
        if (goalIndex === -1) {
            return [];
        }

        const removedActions = this.executedActions.splice(goalIndex);
        this.currentGoalId = null;

        vscode.window.visibleTextEditors.forEach(editor => {
            this.updateDecorations(editor);
        });

        return removedActions;
    }

    private updateDecorations(editor: vscode.TextEditor): void {
        if (!this.isExecutionTrackingEnabled()) {
            editor.setDecorations(this.executedDecorationType, []);
            editor.setDecorations(this.pendingDecorationType, []);
            return;
        }

        const documentActions = this.getActionsForDocument(editor.document.uri.toString());
        const executedDecorations: vscode.DecorationOptions[] = documentActions.map(action => ({
            range: action.range,
        }));

        // Get pending actions for this document
        const pendingDecorations: vscode.DecorationOptions[] = [];
        for (const [actionId, pendingAction] of this.pendingActions) {
            if (pendingAction.editor.document.uri.toString() === editor.document.uri.toString()) {
                pendingDecorations.push({
                    range: pendingAction.range,
                });
            }
        }

        editor.setDecorations(this.executedDecorationType, executedDecorations);
        editor.setDecorations(this.pendingDecorationType, pendingDecorations);
    }

    dispose(): void {
        this.executedDecorationType.dispose();
        this.pendingDecorationType.dispose();
    }
}
