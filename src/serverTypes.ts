
export type Position = [number, number];
export type Location = [start: Position, end: Position];

export type CompilerOutMessage = {
    kind: 'compilerOut',
    pos: Position,
    body: string,
};
export type ToplevelOutMessage = {
    kind: 'toplevelOut',
    pos: Position,
    body: string,
};
export type ErrorMessage = {
    kind: 'error',
    hard: boolean,
    pos: Location,
    msg: string,
};
export type CompileSkipMessage = {
    kind: 'compileSkip',
    pos: Position,
};
export type CompileProgressMessage = {
    kind: 'compileProgress',
    pos: Position,
};
export type CompileCompletedMessage = {
    kind: 'compileCompleted'
};
export type InterruptedMessage = {
    kind: 'interrupted'
};

export type Message = CompilerOutMessage | ToplevelOutMessage | ErrorMessage |
    CompileSkipMessage | CompileProgressMessage | CompileCompletedMessage | InterruptedMessage;

export type PrettyString = string;

export type Color = 'black' | 'maroon' | 'green' | 'olive' | 'navy' | 'purple' | 'teal' | 'gray' |
    'silver' | 'red' | 'lime' | 'yellow' | 'blue' | 'magenta' | 'cyan' | 'white';

export type Style = { FG: Color } | { BG: Color } | "B" | "U" | { u: string }

export type Annotation = 'FV' | 'BV' | 'TyV' | 'TyOp' | 'TySyn' | 'Const' | 'SymConst' |
    'FldName' | 'StringLit' | 'NumLit' | 'CharLit' | { Note: string };

export type PrettyElem = string | {
    style: Style[] | Annotation,
    contents: Pretty,
};

export type Pretty = string | PrettyElem[];

export type TypeHover = {
    kind: 'type',
    pos: Location,
    value: PrettyString,
};

export type DocTxtHover = {
    kind: 'doctxt',
    text: string,
};

export type Markup = string | ['p'] | { code: string } | { emph: string } | { xmpl: string };

export type SectionHeader = 'DOC' | 'SYNOPSIS' | 'COMMENTS' |
    'USES' | 'KEYWORDS' | 'DESCRIBE' | 'FAILURE' | 'EXAMPLE' | 'LIBRARY' | 'STRUCTURE';

export type Section =
    { kind: 'type', value: string } |
    { kind: 'field', header: SectionHeader, value: Markup[] } |
    { kind: 'seeAlso', value: string[] };

export type DocHover = {
    kind: 'doc',
    doc: Section[],
};

export type HoverInfo = TypeHover | DocTxtHover | DocHover;

export type ExtLocation = { file: string, line?: number };

export type DefinitionInfo = [origin: Location, target: Location | ExtLocation];
