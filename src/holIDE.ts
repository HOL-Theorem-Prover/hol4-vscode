import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { log, error, pluralize, holdir } from './common';
import { escapeMLString, HolServer, manpageToMarkdown, prettyStringToMarkdown } from './server';
import { Message } from './serverTypes';

/**
 * Path to where symbol databases are stored in each directory.
 */
const databaseDir = '.hol-vscode';

/**
 * Default locations to search for workspace-external dependencies in. Lines
 * that start with a dollar sign ($) are treated as environment variables.
 */
const externalDirs = ['$HOLDIR'];

/**
 * The kind of entry indexed by the entry database:
 * - Theorem: Regular theorems
 * - Definition: Recursive function definitions
 * - Inductive: Inductive relation definitions
 */

/**
 * Theorem structure for go-to-definition and hover info.
 */
interface HOLEntry {
    name: string;
    statement: string;
    file: string;
    line: number;
    type: 'Theorem' | 'Definition' | 'Inductive';
};

/**
 * Convert a {@link HOLEntry} into a {@link vscode.SymbolInformation}.
 *
 * @returns A {@link vscode.SymbolInformation}.
 */
export function entryToSymbol(entry: HOLEntry): vscode.SymbolInformation {
    return {
        name: entry.name,
        kind: vscode.SymbolKind.Function,
        location: new vscode.Location(
            vscode.Uri.file(entry.file),
            new vscode.Position(entry.line - 1, 0)),
        containerName: '',
    };
};

/**
 * Convert a {@link HOLEntry} into a {@link vscode.CompletionItem}.
 *
 * @returns A {@link vscode.CompletionItemKind}.
 */
export function entryToCompletionItem(entry: HOLEntry): vscode.CompletionItem {
    const item = new vscode.CompletionItem(
        entry.name,
        vscode.CompletionItemKind.Function,
    );
    item.commitCharacters = [' '];
    item.documentation = `${entry.type}: ${entry.name}\n${entry.statement}`;
    return item;
}

/**
 * This class is responsible for maintaining an index of all HOL symbols
 * (theorems, function definitions, rule definitions) in the current workspace,
 * and optionally, for all its dependencies.
 *
 * On construction, it first tries to consult an existing database in the
 * directory {@link databaseDir} in the workspace root. If it does not find this
 * database, it attempts to create it.
 *
 * By default, the database consults the list {@link externalDirs}
 * when indexing dependencies outside of the current workspace. Optionally,
 * the user may create a file called `dependencies.json` in the
 * {@link databaseDir} directory, which lists all dependency directories:
 * ```json
 * [
 *     "foo/bar/baz",
 *     "bar/baz/quux"
 * ]
 * ```
 * When possible, the database will attempt to index these locations as well
 * (as if they were part of the workspace).
 *
 */
export class HOLIDE {

    /**
     * This variable holds the list of imports in the currently active document.
     */
    public imports: { [uri: string]: string[] | undefined } = {};

    /**
     * Database of workspace-local {@link HOLEntry} entries.
     */
    private workspaceIndex: HOLEntry[];

    /**
     * Database of workspace-external {@link HOLEntry} entries.
     */
    private externalIndex: HOLEntry[] = [];

    private servers: { [uri: string]: HolServer | undefined } = {};
    private diagState: { [uri: string]: vscode.Diagnostic[] } = {};

    private prelude: string;
    private postPrelude: string;

    private diags: vscode.DiagnosticCollection = vscode.languages.createDiagnosticCollection('HOL4 diags');

    private loadingSpinner?: vscode.StatusBarItem;

    constructor(
        context: vscode.ExtensionContext,

        /** Path to the HOL installation to use. */
        private holPath: string,

        /** the path to the current workspace root */
        private workspaceDir: string
    ) {
        this.startLoadingSpinner();

        this.prelude = 'val _ = PolyML.print_depth 0;\n';
        for (const file of [
            ...[
                'src/portableML/UC_ASCII_Encode.sig',
                'src/portableML/UC_ASCII_Encode.sml',
                'help/src-sml/ParseDoc.sig',
                'help/src-sml/ParseDoc.sml',
            ].map(f => path.join(holPath, f)),
            ...[
                'tacticParser.sml', 'holide.sml', 'vscodeBase.sml', 'vscode.sml', 'setup.sml'
            ].map(f => context.asAbsolutePath(path.join('resources', f))),
        ]) {
            this.prelude += `val _ = use ${escapeMLString(file)};\n`;
        }
        this.prelude += `structure VSCode = VSCodeProto;\n`;
        this.postPrelude = 'val _ = HOL_IDE.postPrelude ();\n';

        // Collect all `open` declarations in the current document.
        let editor;
        if ((editor = vscode.window.activeTextEditor)) {
            const doc = editor.document;
            const importsSet = new Set<string>();
            getImports(removeComments(doc.getText()), i => importsSet.add(toImport(i)));
            const imports: string[] = [];
            importsSet.forEach(s => imports.push(s));
            this.imports[doc.uri.toString()] = imports;
            this.startServer(doc).then(server => this.compileDocument(server, doc));
        }

        // Read the entry-index in the workspace database.
        //
        // The first time a user opens a new workspace there generally won't be
        // an existing database. If this is the case, query the user about
        // refreshing the database, and then resume as if the index was empty.
        let index = readDatabase(workspaceDir);
        this.workspaceIndex = index ? index : [];

        if (!index) {
            vscode.window.showInformationMessage(
                'HOL: Unable to find workspace index. Refreshing it now.',
            );
            this.refreshIndex();
        }

        // Attempt to read the entry-indices for each listed dependency, and
        // add those entries to `this.externalIndex`. Those paths for which
        // we can't find any entries are added to `unindexed`.
        const unindexed: string[] = [];
        readDependencies(workspaceDir).forEach((depPath) => {
            const entries = readDatabase(depPath);
            if (entries) {
                entries.forEach(entry => this.externalIndex.push(entry));
            } else {
                log(`Unable to index ${depPath}`);
                unindexed.push(depPath);
            }
        });

        // Create indexes for workspace dependencies.
        if (unindexed.length > 0) {
            vscode.window.showInformationMessage(
                `HOL: Indexing ${unindexed.length} external directories`
            );
            this.updateDependencyIndex(unindexed);
        }
    }

    startLoadingSpinner() {
        this.loadingSpinner = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 10);
        this.loadingSpinner.text = '$(loading~spin) Loading HOL...';
        this.loadingSpinner.show();
    }

    /**
     * Refresh the index entries for the provided document.
     *
     * @param document The document to index.
     */
    indexDocument(document: vscode.TextDocument) {
        this.updateWorkspaceIndex([document.uri.fsPath]);
    }

    /**
     * Refresh the index entries for all files in the workspace.
     */
    indexWorkspace() {
        const scripts = findExtFiles(this.workspaceDir, 'Script.sml');
        this.updateWorkspaceIndex(scripts);
    }

    /**
     * Refresh the workspace index entries for each file in the list, and
     * synchronize the entries with the on-disk workspace index in
     * {@link databaseDir}/entries.json. If this file does not exist, then it
     * (and its directory) is created.
     *
     * TODO(oskar.abrahamsson) Lots of duplication in this and {@link indexDep}
     *   and {@link updateDependencyIndex}.
     *
     * @param files Paths to files to refresh the index for.
     */
    private updateWorkspaceIndex(files: string[]) {
        // If the database directory doesn't exist, then create it:
        const outputDir = path.join(this.workspaceDir, databaseDir);
        if (!fs.existsSync(outputDir)) {
            fs.mkdirSync(outputDir);
        }
        const entries = parseFiles(files);

        // Refresh the entries in `workspaceIndex` that referred to any of the
        // files in `files`:
        this.workspaceIndex = this.workspaceIndex.filter(entry => !files.includes(entry.file));
        entries.forEach(entry => this.workspaceIndex.push(entry));

        // Write to disk:
        const outputFile = path.join(outputDir, 'entries.json');
        fs.writeFileSync(outputFile, JSON.stringify(this.workspaceIndex, null, 2));
    }

    /**
     * Indexes the files in the list and returns a list of entries.
     * {@link databaseDir}/entries.json file. Returns a list of updated entries.
     *
     * @param files The files
     * @param dir The directory where the database should be stored.
     * @returns
     */
    private indexDep(files: string[], dir: string): HOLEntry[] {
        // If the database directory does not exist, then create it:
        const outputDir = path.join(dir, databaseDir);
        if (!fs.existsSync(outputDir)) {
            fs.mkdirSync(outputDir);
        }
        const entries = parseFiles(files);

        // Write to disk:
        const outputFile = path.join(outputDir, 'entries.json');
        fs.writeFileSync(outputFile, JSON.stringify(entries, null, 2));

        return entries;
    }

    /**
     * Indexes directories given under the dependencies paths using
     * {@link indexDep}.
     *
     * @param paths Paths to search for HOL scripts to index.
     */
    private updateDependencyIndex(paths: string[]) {
        paths.forEach((depPath) => {
            try {
                const files = findExtFiles(depPath, 'Script.sml');
                this.indexDep(files, depPath).forEach(entry => {
                    this.externalIndex.push(entry);
                });
            } catch (err: unknown) {
                if (err instanceof Error) {
                    error(`Unable to index files in ${depPath}: ${err.message} `);
                }
            }
        });
    }

    /**
     * Refresh the index of the current workspace and all its dependencies.
     */
    refreshIndex() {
        this.indexWorkspace();

        this.updateDependencyIndex(readDependencies(this.workspaceDir));
    }

    updateImports(document: vscode.TextDocument) {
        const importsSet = new Set<string>();
        getImports(removeComments(document.getText()), i => importsSet.add(toImport(i)));
        const imports: string[] = [];
        importsSet.forEach(s => imports.push(s));
        this.imports[document.uri.toString()] = imports;
    }

    /**
     * Calls `f` on all entries in the database: both those local to the current
     * workspace, and external entries.
     */
    forEachEntry(f: (_: HOLEntry) => void) {
        this.workspaceIndex.forEach(f);
        this.externalIndex.forEach(f);
    }

    /**
     * Returns the first entry among all entries (both local and external) satisfying `f`.
     *
     * @returns The first matching result.
     */
    findEntry(f: (_: HOLEntry) => boolean): HOLEntry | undefined {
        return this.workspaceIndex.find(f) || this.externalIndex.find(f);
    }

    /**
     * Returns the list of all {@link HOLEntry} entries that belong to the
     * document.
     *
     * @param document The document for which to return entries.
     * @returns All entries belonging to the current document.
     */
    documentEntries(document: vscode.TextDocument): HOLEntry[] {
        return this.workspaceIndex
            .filter((entry) => entry.file === document.uri.path);
    }

    tryServer(document: vscode.TextDocument): HolServer | undefined {
        const uri = document.uri.toString();
        return this.servers[uri];
    }

    server(document: vscode.TextDocument): HolServer {
        const uri = document.uri.toString();
        const s = this.servers[uri];
        if (s) return s;
        const docPath = path.dirname(document.fileName);
        const server = new HolServer(docPath, this.holPath);
        let progress: vscode.Position | undefined = new vscode.Position(0, 0);
        server.messageListener = (msgs: Message[]) => {
            let dirty = false;
            const newDiags = [];
            for (const e of msgs) {
                switch (e.kind) {
                    case 'compilerOut':
                    case 'toplevelOut': log(e.body); break;
                    case 'compileSkip':
                    case 'compileProgress':
                        if (e.pos[0] || e.pos[1]) {
                            progress = server.utf8ToPosition(e.pos);
                            if (e.kind == 'compileSkip') {
                                newDiags.push(...(this.diags.get(document.uri) ?? [])
                                    .filter(diag => diag.range.end.isBefore(progress!)));
                            }
                            dirty = true;
                        }
                        break;
                    case 'error':
                        newDiags.push(new vscode.Diagnostic(server.utf8ToRange(e.pos), e.msg, e.hard ?
                            vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning));
                        break;
                    case 'compileCompleted':
                    case 'interrupted': progress = undefined; dirty = true; break;
                }
            }
            this.diagState[uri].push(...newDiags);
            if (dirty) {
                if (this.loadingSpinner) {
                    if (progress) {
                        this.loadingSpinner.text =
                            `$(loading~spin) Loading ${path.basename(document.fileName)}... (${progress.line}/${document.lineCount})`;
                    } else {
                        this.loadingSpinner.dispose();
                        this.loadingSpinner = undefined;
                    }
                }
                this.diags.set(document.uri, this.diagState[uri].concat(
                    (this.diags.get(document.uri) ?? [])
                        .filter(diag => progress && diag.range.start.isAfterOrEqual(progress))));
            } else {
                this.diags.set(document.uri, (this.diags.get(document.uri) ?? []).concat(newDiags));
            }
        };
        return this.servers[uri] = server;
    }

    async quietly(server: HolServer, ...s: string[]) {
        const response = await server.request(...s);
        if (this.loadingSpinner) this.loadingSpinner.tooltip = undefined;
        if (response) {
            log(`server was noisy: \n${response}`);
            const start = response.indexOf('error:');
            if (start >= 0) {
                const error = response.substring(start);
                if (this.loadingSpinner) {
                    this.loadingSpinner.text = '$(error) HOL load failed'
                    this.loadingSpinner.tooltip = error
                    this.loadingSpinner.backgroundColor =
                        new vscode.ThemeColor('statusBarItem.errorBackground')
                }
                throw error;
            }
        }
    }

    async startServer(document: vscode.TextDocument): Promise<HolServer> {
        const server = this.server(document);
        await server.ensureRunning(async () => {
            const text = document.getText();
            await this.quietly(server, this.prelude,
                `val _ = VSCode.filename := ${escapeMLString(document.fileName)};\n`);
            const imports: string[] = await server.requestJSON(
                `val _ = VSCode.holdep ${escapeMLString(text)};\n`);
            if (this.loadingSpinner) {
                this.loadingSpinner.text = `$(loading~spin) Loading ${pluralize(imports.length, 'module')}...`;
                this.loadingSpinner.tooltip = `Loading ${imports.join(', ')}`;
                this.loadingSpinner.show();
            }

            const loads = imports.map(s => `val _ = qload "${s}" handle _ => ();\n`);
            if (document.fileName.endsWith('.sml') && !document.fileName.endsWith('Script.sml')) {
                const sigfile = document.fileName.substring(0, document.fileName.length - 4) + '.sig';
                if (fs.existsSync(sigfile)) {
                    loads.push(`val _ = use "${path.basename(sigfile)}";\n`);
                }
            }
            await this.quietly(server, ...loads, this.postPrelude);
            if (this.loadingSpinner) this.loadingSpinner.tooltip = undefined;
        });
        return server;
    }

    async compileDocument(server: HolServer, document: vscode.TextDocument): Promise<void> {
        if (server.lastVersion != document.version) {
            // log(`${Date.now()} setFileContents`);
            this.diagState[document.uri.toString()] = [];
            await server.setFileContents(document.getText(), document.version);
        }
    }

    async ensureCompiled(document: vscode.TextDocument): Promise<HolServer> {
        const server = await this.startServer(document);
        await this.compileDocument(server, document);
        return server;
    }

    async getHoverInfo(
        document: vscode.TextDocument, inRange: vscode.Range, results: vscode.MarkdownString[]
    ): Promise<vscode.Range | undefined> {
        const server = await this.ensureCompiled(document);
        const pos = server.rangeToUtf8(inRange);
        let range: vscode.Range | undefined = undefined;
        for (const hover of await server.getHoverInfo(pos)) {
            switch (hover.kind) {
                case 'type':
                    const range2 = server.utf8ToRange(hover.pos);
                    range = range ? range.union(range2) : range2;
                    results.push(prettyStringToMarkdown(hover.value));
                    break;
                case 'doctxt':
                    results.push((new vscode.MarkdownString).appendCodeblock(hover.text, 'plaintext'));
                    break;
                case 'doc':
                    results.push(manpageToMarkdown(hover.doc));
                    break;
            }
        }
        return range;
    }

    async gotoDefinition(
        document: vscode.TextDocument, position: vscode.Position
    ): Promise<vscode.LocationLink[]> {
        const server = await this.ensureCompiled(document);
        const pos = server.positionToUtf8(position);
        const results: vscode.LocationLink[] = [];
        for (const [origin, target] of await server.gotoDefinition(pos)) {
            const originSelectionRange = server.utf8ToRange(origin);
            if ('file' in target) {
                let lineNr = target.line;
                let line = '';
                let search = document.getText(originSelectionRange);
                search = search.substring(search.lastIndexOf('.') + 1);
                const buffer = await fs.promises.readFile(target.file);
                let start = 0; let end = 0;
                let char = -1;
                if (lineNr !== undefined) {
                    for (let i = 0; ; i++) {
                        end = buffer.indexOf(0x0a, start);
                        if (end < 0) { end = buffer.length; break; }
                        if (i >= lineNr) break;
                        start = end + 1;
                    }
                    line = buffer.toString('utf8', start, end);
                    char = line.search(search);
                } else {
                    let line0 = '';
                    for (lineNr = 0; ; lineNr++) {
                        end = buffer.indexOf(0x0a, start);
                        const last = end < 0;
                        if (last) end = buffer.length;
                        line = buffer.toString('utf8', start, end);
                        if (lineNr == 0) line0 = line;
                        char = line.search(search);
                        if (char >= 0 || last) break;
                        start = end + 1;
                    }
                    if (char < 0) { lineNr = 0; line = line0; }
                }
                results.push({
                    originSelectionRange,
                    targetUri: vscode.Uri.file(target.file),
                    targetRange: char >= 0
                        ? new vscode.Range(lineNr, char, lineNr, char + search.length)
                        : new vscode.Range(lineNr, 0, lineNr, line.length),
                });
            } else {
                results.push({
                    originSelectionRange,
                    targetUri: document.uri,
                    targetRange: server.utf8ToRange(target),
                });
            }
        }
        return results;
    }

    restartServers() {
        for (const s in this.servers) this.servers[s]!.dispose();
        this.diags.clear();
        this.servers = {};
        this.loadingSpinner?.dispose();
        this.loadingSpinner = undefined;

        for (const editor of vscode.window.visibleTextEditors) {
            const doc = editor.document;
            if (doc.languageId == 'hol4' && doc.uri.scheme == 'file') {
                if (!this.loadingSpinner) this.startLoadingSpinner();
                this.startServer(doc).then(server => this.compileDocument(server, doc));
            }
        }
    }

    dispose() {
        for (const s in this.servers) this.servers[s]!.dispose();
        this.diags.dispose();
    }
}

/**
 * Read the contents of the on-disk {@link HOLEntry} database in
 * {@link databaseDir}. Returns `undefined` if the database does not exist,
 * or if {@link databaseDir} does not exist.
 *
 * @param dir The directory to look for the entry database in.
 * @returns A list of {@link HOLEntry} entries, if the database exists.
 */
function readDatabase(dir: string): HOLEntry[] | undefined {

    const outputDir = path.join(dir, databaseDir);
    if (!fs.existsSync(outputDir)) {
        log(`${outputDir} does not exist`);
        return;
    }

    const outputFile = path.join(outputDir, 'entries.json');
    if (!fs.existsSync(outputFile)) {
        log(`${outputFile} does not exist`);
        return;
    }

    try {
        return JSON.parse(fs.readFileSync(outputFile, 'utf-8'));
    } catch (err) {
        if (err instanceof Error) {
            log(`Unable read ${outputFile}: ${err.message} `);
        }
        return;
    }
}

/**
 * Reads the contents of the dependency index from disk, if it exists. The
 * dependency index always contains at least the contents of
 * {@link externalDirs}.
 *
 * @param dir The directory to search in.
 * @returns A list of directories to search for dependencies in.
 */
function readDependencies(dir: string): string[] {
    let paths: string[] = externalDirs;

    const outputFile = path.join(dir, databaseDir, 'dependencies.json');
    if (!fs.existsSync(outputFile)) {
        log(`${outputFile} does not exist, \n` +
            `proceeding with default external dependencies`);
    } else {
        try {
            const contents = fs.readFileSync(outputFile, 'utf-8');
            paths = paths.concat(JSON.parse(contents));
        } catch (err) {
            if (err instanceof Error) {
                log(`Unable to parse ${outputFile}: ${err.message}, \n` +
                    `proceeding with default external dependencies`);
            }
        }
    }
    return paths.flatMap(p => {
        if (!p.startsWith('$')) return [p];
        const envVar = p.slice(1);
        let val = envVar === 'HOLDIR' ? holdir() : undefined;
        if (!val) val = process.env[envVar];
        if (val) return val;
        error(`environment variable \$${envVar} is not defined`);
        return [];
    });
}

/**
 * Returns all files ending in "Script.sml" from the current directory (or any
 * nested directory).
 *
 * @param directory
 * @param ext
 * @returns
 */
function findExtFiles(directory: string, ext: string, smlFiles: string[] = []): string[] {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
        if (entry.isDirectory() && !entry.name.startsWith('.')) {
            findExtFiles(path.join(directory, entry.name), ext, smlFiles);
        } else if (entry.isFile() && entry.name.endsWith(ext)) {
            smlFiles.push(path.join(directory, entry.name));
        }
    }
    return smlFiles;
}

/**
 * Returns the imported theories in the document.
 *
 * @param document Document to scan for imported theories.
 * @returns A list of imports.
 */
export const getImports = (() => {
    const importRegex = /^\s*(local\s*)?open\b/mg;
    const identRegex = /\s+([a-zA-Z][a-zA-Z0-9_']*)\b/my;
    const moduleRegex = /\b([a-zA-Z][a-zA-Z0-9_']*)\.[a-zA-Z][a-zA-Z0-9_']*\b/g;
    const semiRegex = /[\s;]*/my;
    const keywords = new Set([
        'datatype', 'local', 'nonfix', 'prim_val', 'type', 'val', 'end', 'exception',
        'functor', 'signature', 'structure', 'open', 'fun', 'infix', 'infixr', 'in',
        'Theorem', 'Definition', 'Inductive', 'CoInductive', 'Triviality',
        'Datatype', 'Type', 'Overload'
    ]);
    return (text: string, onImport: (imp: string) => void, onOpen: (start: number, end: number) => void = () => { }) => {
        let match: RegExpExecArray | null;
        while (importRegex.exec(text)) {
            let end = identRegex.lastIndex = importRegex.lastIndex;
            const start = end - 4;
            let first = true;
            while ((match = identRegex.exec(text))) {
                const name = match[1];
                if (!first && keywords.has(name)) {
                    if (name == 'open') end = match.index;
                    break;
                }
                onImport(name);
                first = false;
                end = identRegex.lastIndex;
            }
            semiRegex.lastIndex = end;
            semiRegex.exec(text);
            end = semiRegex.lastIndex;
            onOpen(start, end);
            importRegex.lastIndex = end;
        }
        while ((match = moduleRegex.exec(text))) {
            onImport(match[1]);
        }
    }
})();

function toImport(name: string): string {
    const n = name.match(/(\S+)Theory/);
    return n ? n[1] + 'Script.sml' : name;
}


/**
 * Gets comments in the contents of a HOL4 file.
 *
 * @param contents
 * @returns
 */
export function findComments(str: string, onComment: (start: number, end: number) => void) {
    let open = str.indexOf('(*');
    if (open < 0) return;
    let start = open;
    let end = open + 2;
    let close = str.indexOf('*)', end);
    if (close < 0) return;
    let depth = 1;
    open = str.indexOf('(*', end);
    while (true) {
        if (open >= 0 && open < close) {
            depth++;
            end = open + 2;
            open = str.indexOf('(*', end);
        } else {
            end = close + 2;
            if (depth == 1) {
                onComment(start, end);
                if (open < 0) return;
                start = open;
                end = open + 2;
                open = str.indexOf('(*', end);
            } else {
                depth--;
            }
            close = str.indexOf('*)', end);
            if (close < 0) return;
        }
    }
}

/**
 * Removes comments from the contents of a HOL4 file.
 *
 * @param contents
 * @returns
 */
export function removeComments(contents: string): string {
    let index = 0;
    let buffer: string[] = [];
    findComments(contents, (start, end) => {
        const match = contents.substring(start + 2, end - 2);
        const numNewlines = match.split(/\r\n|\n|\r/).length - 1;
        buffer.push(contents.substring(index, start), '\n'.repeat(numNewlines));
        index = end;
    });
    if (!buffer) return contents;
    buffer.push(contents.substring(index));
    return buffer.join('');
}

/**
 * Check whether the entry should be accessible for the given parameters.
 */
export function isAccessibleEntry(
    entry: HOLEntry,
    imports: string[] | undefined,
    document: vscode.TextDocument,
): boolean {
    return imports?.some(imp => entry.file.includes(imp)) ||
        entry.file.includes(document.fileName);
}

/**
 * Try to parse all HOL `Theorem` declarations in a string:
 * ```
 *   Theorem <name><attribute-list>?:
 *   <term>
 *   End
 * ```
 * where `<attribute-list>` is a comma-separated list of identifiers.
 */
const parseTheoremRegex = (() => {
    const theoremRegex = /Theorem\s+(\S+?)\s*:\s+([\s\S]*?)\sProof\s+([\s\S]*?)\sQED/mg;
    const afterIdentifierThingRegex = /\[\S*?\]/mg;
    return (filename: string, contents: string): HOLEntry[] => {
        const entries: HOLEntry[] = [];
        let match: RegExpExecArray | null;
        while ((match = theoremRegex.exec(contents))) {
            entries.push({
                name: match[1].replace(afterIdentifierThingRegex, ''),
                statement: match[2],
                file: filename,
                line: contents.slice(0, match.index).split('\n').length,
                type: 'Theorem',
            });
        }
        return entries;
    }
})();

/**
 * Try to parse all HOL `Definition` declarations in a string:
 * ```
 *   Definition <name>:
 *   <term>
 *   Termination?
 *   <tactics>?
 *   End
 * ```
 */
const parseDefinitions = (() => {
    const definition = /Definition\s+(\S+?)\s*:\s+([\s\S]*?)\sEnd/mg;
    const termination = /([\s\S]*?)Termination\s+([\s\S]*?)\s/;
    const attributes = /\[\S*?\]/mg;
    return (filename: string, contents: string): HOLEntry[] => {
        const entries: HOLEntry[] = [];
        let match: RegExpExecArray | null;
        while ((match = definition.exec(contents))) {
            let statement: RegExpExecArray | null;
            if (match[2].includes('Termination') && (statement = termination.exec(match[2]))) {
                entries.push({
                    name: match[1].replace(attributes, ''),
                    statement: statement[1],
                    file: filename,
                    line: contents.slice(0, match.index).split('\n').length,
                    type: 'Definition',
                });
            } else {
                entries.push({
                    name: match[1].replace(attributes, ''),
                    statement: match[2],
                    file: filename,
                    line: contents.slice(0, match.index).split('\n').length,
                    type: 'Definition',
                });
            }
        }
        return entries;
    }
})();

/**
 * Try to parse all HOL `Define` declarations in a string:
 * ```
 *   val <name> = Define <term>
 * ```
 */
function parseDefines(filename: string, contents: string): HOLEntry[] {
    // TODO(oskar.abrahamsson) Write a function that picks up all Define-style
    //   (old-style definitions).
    return [];
}

/**
 * Try to parse all `store_thm` applications in a string:
 * ```
 *   val ... = store_thm(..., <name>, <term>);
 * ```
 */
function parseStoreThms(filename: string, contents: string): HOLEntry[] {
    const storethmSMLSyntax = /val\s+(\S*)\s*=\s*(?:Q\.)?store_thm\s*\([^,]+,\s+\(?(?:“|`| ``) ([^”`]*)(?:”|` | ``) \)?\s *, [^;] +?;/mg;
    const attributes = /\[\S*?\]/mg;
    const entries: HOLEntry[] = [];
    let match: RegExpExecArray | null;
    while ((match = storethmSMLSyntax.exec(contents))) {
        entries.push({
            name: match[1].replace(attributes, ''),
            statement: match[2],
            file: filename,
            line: contents.slice(0, match.index).split('\n').length,
            type: 'Theorem',
        });
    }
    return entries;
}

/**
 * Try to parse all HOL `Inductive` declarations in a string:
 * ```
 *   Inductive <name>:
 *   <sort-of-term>
 *   End
 * ```
 */
function parseInductives(filename: string, contents: string): HOLEntry[] {
    const inductive = /Inductive\s+(\S+?)\s*:\s+([\s\S]*?)\sEnd/mg;
    const attributes = /\[\S*?\]/mg;
    const entries: HOLEntry[] = [];
    let match: RegExpExecArray | null;
    while ((match = inductive.exec(contents))) {
        entries.push({
            name: match[1].replace(attributes, '') + '_def',
            statement: match[2],
            file: filename,
            line: contents.slice(0, match.index).split('\n').length,
            type: 'Inductive',
        });
    }
    return entries;
}

/**
 * Try to parse all `save_thm` applications in a string:
 * ```
 *   val ... = ...
 * ```
 */
function parseSaveThms(filename: string, contents: string): HOLEntry[] {
    // TODO(kπ) check save_thm syntax, since it's a bit different from store_thm
    const savethmSMLSyntax = /val\s+(\S*)\s*=\s*(?:Q\.)?save_thm\s*\([^,]+,\s+\(?(?:“|`|``)([^”`]*)(?:”|`|``)\)?\s*,[^;]+?;/mg;
    return [];
}

/**
 * Attempt to extract all HOL definitions, rule definitions, and theorems from
 * a file.
 *
 * @param filename Name of the file that's being parsed.
 * @param data Contents of the file that's being parsed.
 * @returns A list of parsed {@link HOLEntry} entries.
 */
function parseScriptSML(filename: string, data: string): HOLEntry[] {
    const contents = removeComments(data);
    return parseTheoremRegex(filename, contents)
        .concat(parseDefinitions(filename, contents))
        .concat(parseDefines(filename, contents))
        .concat(parseSaveThms(filename, contents))
        .concat(parseStoreThms(filename, contents))
        .concat(parseInductives(filename, contents));
}

/**
 * Reads the files in the list and parses their contents for
 * {@link HOLEntry} entries.
 *
 * TODO(oskar.abrahamsson) This will throw if some file does not exist, or
 *   if we can't read it for whatever reason.
 *
 * TODO(oskar.abrahamsson) Theory names will confuse the plugin.
 *
 * @param files List of files to parse.
 * @returns A list of {@link HOLEntry} entries.
 */
function parseFiles(files: string[]): HOLEntry[] {
    let entries: HOLEntry[] = [];
    files.forEach((filename) => {
        const contents = fs.readFileSync(filename, 'utf-8');
        const parsed = parseScriptSML(filename, contents);
        parsed.forEach((entry) => {
            entry.file = filename;
            entries.push(entry);
        });
    });
    return entries;
}
