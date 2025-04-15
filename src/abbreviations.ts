/// Adapted from https://github.com/leanprover/vscode-lean4/tree/4c7cbdd/lean4-unicode-input, Apache License
import { assert, error } from 'console'
import {
    commands, Disposable, extensions, Hover, HoverProvider, languages,
    Range as LCRange, Position, Selection, TextDocument, TextEditor, window, workspace
} from 'vscode'
import * as abbreviations from './unicode-completions.json'
import { hol4selector, KERNEL_ID } from './common'

const symbolsByAbbreviation: { [abbrev: string]: string } = abbreviations

let cache: Record<string, string | undefined> = {}

function findSymbolsByAbbreviationPrefix(abbrevPrefix: string): string[] {
    const matchingAbbreviations = Object.keys(
        symbolsByAbbreviation
    ).filter(abbrev => abbrev.startsWith(abbrevPrefix))

    matchingAbbreviations.sort((a, b) => a.length - b.length)
    return matchingAbbreviations.map(abbr => symbolsByAbbreviation[abbr])
}

function collectAllAbbreviations(symbol: string): string[] {
    return Object.entries(symbolsByAbbreviation)
        .filter(([_, sym]) => sym === symbol)
        .map(([abbr, _]) => abbr)
}

function findAutoClosingAbbreviations(openingSymbol: string): [string, string][] {
    return Object.entries(symbolsByAbbreviation)
        .filter(([_, sym]) => sym.startsWith(`${openingSymbol}$CURSOR`))
        .map(([abbr, sym]) => [abbr, sym.replace(`${openingSymbol}$CURSOR`, '')])
}

function findSymbolsIn(symbolPlusUnknown: string): string[] {
    const result = new Set<string>()
    for (const [_, sym] of Object.entries(symbolsByAbbreviation)) {
        if (symbolPlusUnknown.startsWith(sym)) {
            result.add(sym)
        }
    }
    return [...result.values()]
}

function getReplacementText(abbrev: string): string | undefined {
    function _getReplacementText(abbrev: string): string | undefined {
        if (abbrev.length === 0) {
            return undefined
        }

        const matchingSymbol = findSymbolsByAbbreviationPrefix(abbrev)[0]
        if (matchingSymbol) {
            return matchingSymbol
        }

        // Convert the `alp` in `\alp7`
        const prefixReplacement = getReplacementText(abbrev.slice(0, abbrev.length - 1))
        if (prefixReplacement) {
            return prefixReplacement + abbrev.slice(abbrev.length - 1)
        }

        return undefined
    }

    if (abbrev in cache) {
        return cache[abbrev]
    }
    const result = _getReplacementText(abbrev)
    cache[abbrev] = result
    return result
}

function getSymbolForAbbreviation(abbrev: string): string | undefined {
    return symbolsByAbbreviation[abbrev]
}

/**
 * A general purpose range implementation.
 * Is offset/length based in contrast to `vscode.Range` which is line/column based.
 */
class Range {
    constructor(readonly offset: number, readonly length: number) {
        assert(length >= 0)
    }

    contains(offset: number): boolean {
        return this.offset <= offset && offset <= this.offsetEnd
    }

    get offsetEnd(): number {
        return this.offset + this.length - 1
    }

    get isEmpty(): boolean {
        return this.length === 0
    }

    toString(): string {
        return `[${this.offset}, +${this.length})`
    }

    move(delta: number): Range {
        return new Range(this.offset + delta, this.length)
    }

    moveKeepEnd(delta: number): Range {
        assert(delta <= this.length)
        const result = new Range(this.offset + delta, this.length - delta)
        assert(result.offsetEnd === this.offsetEnd)
        return result
    }

    moveEnd(delta: number): Range {
        return new Range(this.offset, this.length + delta)
    }

    withLength(newLength: number): Range {
        return new Range(this.offset, newLength)
    }

    containsRange(other: Range): boolean {
        /*
         *     0  1  2  3  4  5
         *       |#  #  #       this            { offset: 1, end: 3, len: 3 }
         *    |              |  other: false    { offset: 0, end: -1, len: 0 }
         *       |  |  |  |     other: true     { offset: i, end: i - 1, len: 0 }
         *       |# |# |#       other: true
         *    |#  #    |#  #    other: false
         *       |#  #  #       other: true
         */
        // If other is non-empty, this must contain all its points.

        return this.offset <= other.offset && other.offsetEnd <= this.offsetEnd
    }

    /**
     * Check whether this range if after `range`.
     */
    isAfter(range: Range): boolean {
        /*
         *     0  1  2  3  4  5
         *       |#  #  #       this
         *    |  |              other: true
         *    |#                other: true
         *       |#             other: false
         *    |#  #             other: false
         */
        return range.offsetEnd < this.offset
    }

    /**
     * Check whether this range if before `range`.
     */
    isBefore(range: Range): boolean {
        /*
         *     0  1  2  3  4  5
         *       |#  #  #       this
         *                |  |  other: true
         *                |#    other: true
         *             |#       other: false
         *             |        other: false
         *             |#  #    other: false
         */
        return range.offset > this.offsetEnd
    }
}

class TrackedAbbreviation {
    constructor(
        public abbreviationRange: Range,
        public abbreviation: string
    ) { }

    range(): Range {
        return this.abbreviationRange.moveKeepEnd(-1)
    }

    matchingSymbol(): string | undefined {
        return getReplacementText(this.abbreviation)
    }

    /**
     * Does this abbreviation uniquely identify a symbol and is it complete?
     */
    isAbbreviationUniqueAndComplete(): boolean {
        return findSymbolsByAbbreviationPrefix(this.abbreviation).length === 1 &&
            !!getSymbolForAbbreviation(this.abbreviation)
    }

    /**
     * Indicates whether this abbreviation has been continued with non-abbreviation characters.
     * Such abbreviations should be replaced immediately.
     */
    finished = false

    processChange(range: Range, newText: string): { shouldStopTracking: boolean; isAffected: boolean } {
        if (this.abbreviationRange.containsRange(range)) {
            this.finished = false

            if (this.abbreviationRange.isBefore(range)) {
                // `newText` is appended to `this.abbreviation`
                if (findSymbolsByAbbreviationPrefix(this.abbreviation + newText).length === 0) {
                    // newText is not helpful anymore. Finish this and don't accept the change.
                    this.finished = true
                    return {
                        shouldStopTracking: false,
                        isAffected: false,
                    }
                }
            }

            this.abbreviationRange = this.abbreviationRange.moveEnd(newText.length - range.length)
            const startStr = this.abbreviation.substring(0, range.offset - this.abbreviationRange.offset)
            const endStr = this.abbreviation.substring(range.offsetEnd + 1 - this.abbreviationRange.offset)
            this.abbreviation = startStr + newText + endStr

            return { shouldStopTracking: false, isAffected: true }
        } else if (range.isBefore(this.range())) {
            // The changed happened before us. We need to move.
            this.abbreviationRange = this.abbreviationRange.move(newText.length - range.length)
            return { shouldStopTracking: false, isAffected: false }
        } else if (range.isAfter(this.range())) {
            // The change does not affect us.
            return { shouldStopTracking: false, isAffected: false }
        } else {
            // We cannot process the change. Abort tracking.
            return { shouldStopTracking: true, isAffected: false }
        }
    }
}

class AbbreviationConfig {
    public eagerReplacement =
        workspace.getConfiguration('hol4-mode').get('eagerReplacement', true)
    public abbreviationCharacter =
        workspace.getConfiguration('hol4-mode').get('input.leader', '\\')
}

type Replacement = {
    range: Range
    newText: string
    cursorOffset?: number
}

type SelectionMoveMode =
    | { kind: 'OnlyMoveCursorSelections'; updateUnchangedSelections: boolean }
    | { kind: 'MoveAllSelections' }

class AbbreviationRewriter {
    private readonly disposables = new Array<Disposable>()
    /**
     * All tracked abbreviations are disjoint.
     */
    private readonly trackedAbbreviations = new Set<TrackedAbbreviation>()
    private readonly decorationType = window.createTextEditorDecorationType({
        textDecoration: 'underline',
    })

    private isVimExtensionInstalled = false

    private checkIsVimExtensionInstalled() {
        this.isVimExtensionInstalled = extensions.getExtension('vscodevim.vim') !== undefined
    }

    private doNotTrackNewAbbr = false

    constructor(
        private readonly config: AbbreviationConfig,
        private readonly textEditor: TextEditor
    ) {
        this.checkIsVimExtensionInstalled()
        this.disposables.push(
            this.decorationType,

            workspace.onDidChangeTextDocument(async e => {
                if (e.document !== this.textEditor.document) {
                    return
                }
                const changes = e.contentChanges.slice(0)
                // We need to process the changes at the bottom first.
                // Otherwise, changes at the top will move spans at the bottom down.
                changes.sort((c1, c2) => c2.rangeOffset - c1.rangeOffset)

                for (const c of changes) {
                    const range = new Range(c.rangeOffset, c.rangeLength)
                    this.processChange(range, c.text)
                }

                // Replace any tracked abbreviation that is either finished or unique.
                await this.forceReplace(
                    [...this.trackedAbbreviations].filter(abbr =>
                        abbr.finished ||
                        (this.config.eagerReplacement &&
                            abbr.isAbbreviationUniqueAndComplete())
                    )
                )

                this.updateState()
            }),

            window.onDidChangeTextEditorSelection(async e => {
                if (e.textEditor.document !== this.textEditor.document) {
                    return
                }

                // Replace any tracked abbreviation that lost selection.
                await this.forceReplace(
                    [...this.trackedAbbreviations].filter(abbr =>
                        !e.selections.some(s => abbr.range().containsRange(
                            fromVsCodeRange(s, e.textEditor.document).withLength(0)))
                    )
                )

                this.updateState()
            }),

            commands.registerTextEditorCommand('hol4-mode.input.convert', async () => {
                this.forceReplace([...this.trackedAbbreviations])
            }),

            extensions.onDidChange(_ => this.checkIsVimExtensionInstalled())
        )
    }

    private async forceReplace(abbreviations: TrackedAbbreviation[]): Promise<void> {
        if (abbreviations.length === 0) {
            return
        }
        for (const a of abbreviations) {
            this.trackedAbbreviations.delete(a)
        }

        // Wait for VS Code to trigger `onDidChangeTextEditorSelection`
        // await waitForNextTick()

        const cursorVar = '$CURSOR'
        const replacements: Replacement[] = []
        for (const abbr of abbreviations) {
            const symbol = abbr.matchingSymbol()
            if (symbol) {
                const newText = symbol.replace(cursorVar, '')
                let cursorOffset: number | undefined = symbol.indexOf(cursorVar)
                if (cursorOffset === -1) {
                    cursorOffset = undefined
                }
                replacements.push({
                    range: abbr.range(),
                    newText,
                    cursorOffset,
                })
            }
        }
        // Process replacements with lowest offset first
        replacements.sort((a, b) => a.range.offset - b.range.offset)

        // We don't want replaced symbols (e.g. "\") to trigger abbreviations.
        this.doNotTrackNewAbbr = true
        let ok = await this.replaceAbbreviations(replacements)
        this.doNotTrackNewAbbr = false

        if (ok) {
            this.moveSelections(replacements)
        } else {
            // If replacing the abbreviation did not succeed, keep it around so that we can re-try next time
            // when the text document was changed, the cursor was moved around or the replacement was triggered
            // manually.
            for (const a of abbreviations) {
                this.trackedAbbreviations.add(a)
            }
        }
    }

    private async replaceAbbreviations(replacements: Replacement[]): Promise<boolean> {
        let ok = false
        let retries = 0
        try {
            // The user may have changed the text document in-between `this.textEditor` being updated
            // (when the call to the extension was started) and `this.textEditor.edit()` being executed.
            // In this case, since the state of the editor that the extension sees and the state that
            // the user sees are different, VS Code will reject the edit.
            // This occurs especially often in setups with increased latency until the extension is triggered,
            // e.g. an SSH setup. Since VS Code does not appear to support an atomic read -> write operation,
            // unfortunately the only thing we can do here is to retry.
            while (!ok && retries < 10) {
                ok = await this.textEditor.edit(builder => {
                    for (const r of replacements) {
                        builder.replace(toVsCodeRange(r.range, this.textEditor.document), r.newText)
                    }
                })
                retries++
            }
        } catch (e) {
            // The 'not possible on closed editors' error naturally occurs when we attempt to replace abbreviations as the user
            // is switching away from the active tab.
            if (!(e instanceof Error) || e.message !== 'TextEditor#edit not possible on closed editors') {
                error('while replacing abbreviation: ' + e)
            }
        }
        return ok
    }

    private moveSelections(replacements: Replacement[]) {
        if (!(this.isVimExtensionInstalled || replacements.some(r => r.cursorOffset))) {
            return
        }

        // Process replacements with lowest offset first
        replacements.sort((a, b) => a.range.offset - b.range.offset)

        const replacementInfo = new Array<{
            rangeBeforeEdit: Range
            rangeAfterEdit: Range
            cursorOffset?: number
        }>()
        let totalOffsetShift = 0
        for (const r of replacements) {
            const newText = r.newText
            const rangeBeforeEdit = r.range
            // Re-adjust range to account for new length and changes in prior lengths.
            const rangeAfterEdit = new Range(rangeBeforeEdit.offset + totalOffsetShift, newText.length)
            replacementInfo.push({
                rangeBeforeEdit,
                rangeAfterEdit,
                cursorOffset: r.cursorOffset,
            })
            totalOffsetShift += newText.length - rangeBeforeEdit.length
        }

        this.textEditor.selections = this.textEditor.selections
            .map(s => {
                const r = fromVsCodeRange(s, this.textEditor.document);
                for (const info of replacementInfo) {
                    if (info.cursorOffset === undefined) {
                        // Only move cursor if abbreviation contained $CURSOR
                        continue
                    }
                    const isCursorAtEndOfAbbreviation = r.offset === info.rangeAfterEdit.offsetEnd + 1
                    // Safety check: Prevents moving the cursor if e.g. the replacement triggered
                    // because the selection was moved away from the abbreviation.
                    if (isCursorAtEndOfAbbreviation) {
                        // Move cursor to the position of $CURSOR
                        const sr = new Range(info.rangeAfterEdit.offset + info.cursorOffset, r.length)
                        const { start, end } = toVsCodeRange(sr, this.textEditor.document)
                        return new Selection(start, end)
                    }
                }
                return s
            })
    }

    async replaceAllTrackedAbbreviations() {
        await this.forceReplace([...this.trackedAbbreviations])
        this.updateState()
    }

    private updateState() {
        this.textEditor.setDecorations(
            this.decorationType,
            [...this.trackedAbbreviations].map((a) =>
                toVsCodeRange(a.range(), this.textEditor.document)
            )
        )

        void this.setInputActive(this.trackedAbbreviations.size > 0)
    }

    private async setInputActive(isActive: boolean) {
        await commands.executeCommand('setContext', 'hol4-mode.input.isActive', isActive)
    }

    private processChange(range: Range, text: string) {
        let isAnyTrackedAbbrAffected = false
        for (const abbr of [...this.trackedAbbreviations]) {
            const { isAffected, shouldStopTracking } = abbr.processChange(range, text)
            if (isAffected) {
                isAnyTrackedAbbrAffected = true
            }
            if (shouldStopTracking) {
                this.trackedAbbreviations.delete(abbr)
            }
        }

        if (text === this.config.abbreviationCharacter && !isAnyTrackedAbbrAffected && !this.doNotTrackNewAbbr) {
            this.trackedAbbreviations.add(
                new TrackedAbbreviation(new Range(range.offset + 1, 0), ''))
        }
    }

    dispose() {
        for (const d of this.disposables) {
            d.dispose()
        }
    }
}

function fromVsCodeRange(range: LCRange, doc: TextDocument): Range {
    const start = doc.offsetAt(range.start)
    const end = doc.offsetAt(range.end)
    return new Range(start, end - start)
}

function toVsCodeRange(range: Range, doc: TextDocument): LCRange {
    const start = doc.positionAt(range.offset)
    const end = doc.positionAt(range.offsetEnd + 1)
    return new LCRange(start, end)
}

function waitForNextTick(): Promise<void> {
    return new Promise((res) => setTimeout(res, 0))
}

class AbbreviationHoverProvider implements HoverProvider {
    constructor(private readonly config: AbbreviationConfig) { }

    provideHover(document: TextDocument, pos: Position): Hover | undefined {
        const context = document.lineAt(pos.line).text.substring(pos.character)
        const symbolsAtCursor = findSymbolsIn(context)
        if (symbolsAtCursor.length == 0) return undefined
        const allAbbrevs = symbolsAtCursor.map(symbol => ({
            symbol,
            abbrevs: collectAllAbbreviations(symbol),
        }))
        if (allAbbrevs.every(a => a.abbrevs.length === 0)) return undefined

        const leader = this.config.abbreviationCharacter

        const hoverMarkdown = allAbbrevs
            .map(
                ({ symbol, abbrevs }) => {
                    const abbrevInfo = `Type ${symbol} using ${abbrevs.map(a => '`' + leader + a + '`').join(' or ')}`
                    const autoClosingAbbrevs = findAutoClosingAbbreviations(symbol)
                    const autoClosingInfo =
                        autoClosingAbbrevs.length === 0
                            ? ''
                            : `. ${symbol} can be auto-closed with ${autoClosingAbbrevs
                                .map(([a, closingSym]) => `${closingSym} using \`${leader}${a}\``)
                                .join(' or ')}.`
                    return abbrevInfo + autoClosingInfo
                }
            )
            .join('\n\n')

        const maxSymbolLength = Math.max(...allAbbrevs.map(a => a.symbol.length))
        const hoverRange = new LCRange(pos, pos.translate(0, maxSymbolLength))
        return new Hover(hoverMarkdown, hoverRange)
    }
}

export class AbbreviationFeature {
    private readonly disposables = new Array<Disposable>()
    private readonly config: AbbreviationConfig = new AbbreviationConfig()

    private rewriter: AbbreviationRewriter | undefined

    private setEditor(e: TextEditor | undefined) {
        if (e) {
            if (languages.match(hol4selector, e.document) == 0) {
                e = undefined
            }
        }
        this.rewriter?.dispose()
        this.rewriter = e ? new AbbreviationRewriter(this.config, e) : undefined
    }

    constructor() {
        this.setEditor(window.activeTextEditor)
        this.disposables.push(
            languages.registerHoverProvider(
                KERNEL_ID, new AbbreviationHoverProvider(this.config)),
            window.onDidChangeActiveTextEditor(this.setEditor.bind(this)))
    }

    dispose() {
        for (const d of this.disposables) {
            d.dispose()
        }
        this.rewriter?.dispose()
    }
}

