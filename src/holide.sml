structure HOL_IDE = struct
  val noCompile: PolyML.Compiler.compilerParameters list = []
end;
(*
let (* autoconf-like hack *)
  val s = "structure HOL_IDE = struct\nval noCompile = [PolyML.Compiler.CPNoCompile true]\nend"
  val i = ref 0
  fun read () = (SOME (String.sub (s, !i)) before i := !i + 1) handle Subscript => NONE
  in PolyML.compiler (read, []) () handle _ => () end; (* <- important semicolon *)
*)

structure HOL_IDE: sig

type error =
  {context: PolyML.pretty option, hard: bool, location: PolyML.location, message: PolyML.pretty}

type subtree = PolyML.parseTree option
type trees = PolyML.parseTree list

val prelude: unit -> unit
val postPrelude: unit -> unit

val compile: bool ref

val initialize:
  { text: string,
    filename: string,
    parseError: int * int -> string -> unit,
    compilerOut: string -> unit,
    toplevelOut: string -> unit,
    progress: int -> unit,
    error: error -> unit,
    runtimeExn: exn -> unit,
    mlParseTree: PolyML.parseTree -> unit,
    holParseTree: HolParser.Simple.decl -> unit
  } -> unit

val moveUp: subtree -> subtree
val moveDown: subtree -> subtree
val moveLeft: subtree -> subtree
val moveRight: subtree -> subtree
val printTree: int -> subtree -> PolyML.pretty option
val navigateTo: subtree -> {startOffset: int, endOffset: int} -> subtree
val navigateTo': trees -> {startOffset: int, endOffset: int} -> subtree

val at: PolyML.parseTree list -> int list -> subtree

datatype built = Built of (int * int) * PolyML.ptProperties list * built list
val build: PolyML.parseTree -> built
val buildList: PolyML.parseTree option -> built list

end =
struct
open HOL_IDE

type error =
  {context: PolyML.pretty option, hard: bool, location: PolyML.location, message: PolyML.pretty}

type subtree = PolyML.parseTree option
type trees = PolyML.parseTree list

fun prelude () = Tactical.set_prover (fn (t, _) => mk_oracle_thm "fast_proof" ([], t))

fun postPrelude () = ()

val compile = ref true

fun initialize {
  text, filename, parseError, compilerOut, toplevelOut, progress, error,
  runtimeExn, mlParseTree, holParseTree
} = let
  datatype Chunk
    = RegularChunk of int * substring
    | FlatChunk of int option * substring
    | EOFChunk

  val sr = ref text
  val queue = ref []
  fun push chunk = queue := chunk :: !queue
  fun encode f (i, s) = let
    val j = i + #2 (Substring.base s)
    in f (fn s => push (FlatChunk (SOME j, Substring.full s))) (i, s) end
  val {feed, regular, finishThmVal, doDecl, ...} =
    HolParser.ToSML.mkPushTranslatorCore {
      filename = filename, parseError = parseError, quietOpen = true,
      read = fn _ => !sr before sr := ""
    } {
      regular = push o RegularChunk,
      aux = fn s => push (FlatChunk (NONE, Substring.full s)),
      strstr = encode HolParser.ToSML.strstr,
      strcode = encode HolParser.ToSML.strcode
    }
  val atEnd = ref false
  val pos = ref 0
  fun readChunk () =
    case !queue of
      s :: rest => (queue := rest; s)
    | [] => if !atEnd then EOFChunk else (
      case feed () of
        HolParser.Simple.TopDecl d => (holParseTree d; pos := doDecl true (!pos) d)
      | HolParser.Simple.EOF p =>
        (regular (!pos, p); finishThmVal (); pos := p; atEnd := true);
      queue := rev (!queue);
      readChunk ())

  datatype State
    = Reading of (int * bool) * int * int * string
    | EOF of int
  fun toState start = fn
      EOFChunk => EOF start
    | RegularChunk (base, ss) => let
      val (s, lo, len) = Substring.base ss
      in Reading ((base, true), lo, lo + len, s) end
    | FlatChunk (i, ss) => let
      val (s, lo, len) = Substring.base ss
      in Reading ((Option.getOpt (i, start), false), lo, lo + len, s) end
  val curToken = ref (toState 0 (readChunk ()))
  fun read2 () =
    case !curToken of
      EOF _ => NONE
    | Reading (base, lo, hi, s) =>
      if lo+1 < hi then
        (curToken := Reading (base, lo+1, hi, s); SOME (String.sub(s, lo)))
      else (
        curToken := toState (if #2 base then #1 base + hi else #1 base) (readChunk ());
        if lo+1 = hi then SOME (String.sub(s, lo)) else read2 ())
  fun getOffset () = case !curToken of
      Reading ((base, flat), lo, hi, s) => if flat then base + lo else base
    | EOF pos => pos
  val serial = ref 1
  val result = ref []
  fun ptFn NONE = ()
    | ptFn (SOME pt) = mlParseTree pt
  fun codeFn NONE () = ()
    | codeFn (SOME code) () = let
      val {fixes, values, structures, signatures, functors, types} = code ()
      fun enter f = app (f PolyML.globalNameSpace)
      in enter #enterFix fixes; enter #enterType types; enter #enterSig signatures;
         enter #enterStruct structures; enter #enterFunct functors; enter #enterVal values end
  open PolyML.Compiler
  val parameters = (if !compile then [] else noCompile) @ [
    CPOutStream compilerOut,
    CPPrintStream toplevelOut,
    CPErrorMessageProc error,
    CPCompilerResultFun (fn (pt, code) => (ptFn pt; codeFn code)),
    CPLineOffset getOffset,
    CPPrintInAlphabeticalOrder false,
    CPBindingSeq (fn () => (fn n => n before serial := n + 1) (!serial))];
  fun loop () = (
    progress (getOffset ());
    case !curToken of
      EOF _ => ()
    | _ => ((PolyML.compiler (read2, parameters) () handle e => runtimeExn e); loop ()))
  in loop () end;

fun moveUp NONE = NONE
  | moveUp (SOME (_, props)) = let
    fun find [] = NONE
      | find (PolyML.PTparent p :: _) = SOME (p ())
      | find (_ :: tl) = find tl
    in find props end

fun moveDown NONE = NONE
  | moveDown (SOME (_, props)) = let
    fun find [] = NONE
      | find (PolyML.PTfirstChild p :: _) = SOME (p ())
      | find (_ :: tl) = find tl
    in find props end

fun moveLeft NONE = NONE
  | moveLeft (SOME (_, props)) = let
    fun find [] = NONE
      | find (PolyML.PTpreviousSibling p :: _) = SOME (p ())
      | find (_ :: tl) = find tl
    in find props end

fun moveRight NONE = NONE
  | moveRight (SOME (_, props)) = let
    fun find [] = NONE
      | find (PolyML.PTnextSibling p :: _) = SOME (p ())
      | find (_ :: tl) = find tl
    in find props end

fun printTree _ NONE = NONE
  | printTree n (SOME (_, props)) = let
    fun find [] = NONE
      | find (PolyML.PTprint p :: _) = SOME (p n)
      | find (_ :: tl) = find tl
    in find props end

fun at ls (n::rest) =
    let fun at' [] = I
          | at' (i::rest) = at' rest o funpow i moveRight o moveDown
    in at' rest (SOME (List.nth (ls, n))) end
  | at _ _ = raise Match

datatype built = Built of (int * int) * PolyML.ptProperties list * built list

fun build (tree as ({startPosition, endPosition, ...}, props)) =
  Built ((startPosition, endPosition), props, buildList (moveDown (SOME tree)))

and buildList NONE = []
  | buildList (tree as SOME t) = build t :: buildList (moveRight tree)

fun navigateTo NONE _ = NONE
  | navigateTo (tree as (SOME ({ startPosition, endPosition, ... }, _)))
               (target as {startOffset, endOffset}) =
    if startOffset >= startPosition andalso endOffset <= endPosition
    then (* It's this node or a child. *)
      case moveDown tree of
        NONE => tree (* No children. *)
      | SOME child => let
        (* See which child it is. *)
        fun findChild (result as ({startPosition, endPosition, ...}, _)) =
          if startOffset >= startPosition andalso endOffset <= endPosition
          then SOME result
          else
            case moveRight (SOME result) of
              NONE => NONE
            | SOME next => findChild next
        in
          case findChild child of
            NONE => tree (* In this *)
          | SOME child => navigateTo (SOME child) target
        end
    else (* Must go out. *)
      navigateTo (moveUp tree) target

fun navigateTo' [] _ = NONE
  | navigateTo' ((tree as ({ startPosition, ... }, _)) :: trees)
                (target as {startOffset, ...}) =
    if startOffset < startPosition
    then navigateTo' trees target
    else navigateTo (SOME tree) target

end;
