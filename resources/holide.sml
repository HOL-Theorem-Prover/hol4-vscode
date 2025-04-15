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

val initialize:
  { wrapTactics: bool,
    text: string,
    filename: string,
    parseError: int * int -> string -> unit,
    holParseTree: HolLex.UserDeclarations.decl -> unit,
    tacticBlock: int * int * (int * int) tac_expr -> unit
  } ->
  { compile: bool,
    compilerOut: string -> unit,
    toplevelOut: string -> unit,
    progress: int -> unit,
    error: error -> unit,
    runtimeExn: exn -> unit,
    mlParseTree: PolyML.parseTree -> unit
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

fun prelude () = let
  val _ = PolyML.Compiler.reportUnreferencedIds := true
  val _ = PolyML.Compiler.printInAlphabeticalOrder := false
  val _ = PolyML.Compiler.maxInlineSize := 80
  fun f (t, _) = mk_oracle_thm "fast_proof" ([], t)
  fun f2 g = (
    if current_theory () = "scratch"
    then HOL_WARNING "HOL_IDE" "prove" "calling prove before new_theory"
    else Tactical.set_prover f;
    f g)
  in Tactical.set_prover f2 end

fun postPrelude () = ()

datatype chunk
  = RegularChunk of int * substring
  | FlatChunk of int option * substring
  | EOFChunk

fun pullChunks {wrapTactics, text, filename, parseError, holParseTree, tacticBlock} = let
  val sr = ref text
  val queue = ref []
  fun push chunk = queue := chunk :: !queue
  fun encode f (i, s) = let
    val j = i + #2 (Substring.base s)
    in f (fn s => push (FlatChunk (SOME j, Substring.full s))) (i, s) end
  fun aux s = push (FlatChunk (NONE, Substring.full s))
  val {feed, regular, finishThmVal, doDecl, ...} =
    HolParser.ToSML.mkPushTranslatorCore {
      filename = filename, parseError = parseError, quietOpen = true,
      read = fn _ => !sr before sr := ""
    } {
      regular = push o RegularChunk,
      aux = aux,
      strstr = encode HolParser.ToSML.strstr,
      strcode = encode HolParser.ToSML.strcode
    }
  fun reparseTacticBlock (HolParser.Simple.Decls {start, stop, ...}) = let
    fun processChunks chunks = let
      val body = Substring.concat $ C map chunks (fn
          RegularChunk (_, ss) => ss
        | FlatChunk (_, ss) => ss
        | EOFChunk => Substring.full "")
      val inbox = ref chunks
      fun pushN n start = if n = 0 then start else
        case !inbox of
          (chunk as RegularChunk (base, ss)) :: rest => let
          val (_, lo, len) = Substring.base ss
          in
            if len <= n then (
              queue := chunk :: !queue;
              inbox := rest;
              pushN (n - len) (base + lo + len))
            else let
              val (ss1, ss2) = Substring.splitAt (ss, n)
              val _ = queue := RegularChunk (base, ss1) :: !queue
              val _ = inbox := RegularChunk (base, ss2) :: rest
              in base + lo + n end
          end
        | (chunk as FlatChunk (i, ss)) :: rest =>let
          val len = Substring.size ss
          val start = Option.getOpt (i, start)
          in
            if len <= n then (
              queue := chunk :: !queue;
              inbox := rest;
              pushN (n - len) start)
            else let
              val (ss1, ss2) = Substring.splitAt (ss, n)
              val _ = queue := FlatChunk (i, ss1) :: !queue
              val _ = inbox := FlatChunk (i, ss2) :: rest
              in start end
          end
        | _ => start
      val blockPos = ref 0
      val pos = ref start
      fun tr i = (pos := pushN (i - !blockPos) (!pos); blockPos := i; !pos)
      fun f isTac (start, stop) = let
        val start' = tr start
        val _ = if isTac andalso wrapTactics then
          app aux ["(VSCode.wrapTactic ", Int.toString start', " ("]
        else ()
        in (start', stop) end
      fun g isTac (start', stop) = let
        val stop' = tr stop
        val _ = if isTac andalso wrapTactics then
          app aux [") ", Int.toString stop', ")"]
        else ()
        in (start', stop') end
      open TacticParser
      fun repair _ s = if s = "" then () else (
        parseError (!pos, !pos) ("missing '"^s^"' inserted");
        aux s)
      val () = tacticBlock (start, stop, mapTacExpr (f, g, repair) $ parseTacticBlock body)
      in queue := List.revAppend (!inbox, !queue) end
    fun goMid [] acc _ = acc
      | goMid (chunk :: chunks) acc after =
        if case chunk of
            RegularChunk (base, ss) => base + #2 (Substring.base ss) <= start
          | _ => false
        then let
          val _ = queue := chunks
          val _ = processChunks (chunk :: acc)
          in List.revAppend (!queue, after) end
        else goMid chunks (chunk :: acc) after
    fun goEnd [] acc = acc
      | goEnd (chunk :: chunks) acc =
        if case chunk of
            RegularChunk (base, ss) => base + #2 (Substring.base ss) >= stop
          | _ => true
        then goEnd chunks (chunk :: acc)
        else goMid (chunk :: chunks) [] acc
    in goEnd (!queue) [] end
  val pos = ref 0
  fun pull () = (
    queue := [];
    case feed () of
      HolParser.Simple.TopDecl d => (false, (
      holParseTree d;
      pos := doDecl true (!pos) d;
      case d of
        HolParser.Simple.DefinitionDecl {termination = SOME {decls, ...}, ...} =>
        reparseTacticBlock decls
      | HolParser.Simple.TheoremDecl {body, ...} => reparseTacticBlock body
      | _ => rev (!queue)))
    | HolParser.Simple.EOF p =>
      (regular (!pos, p); finishThmVal (); pos := p; (true, rev (!queue))))
  in pull end

fun pass1 args = let
  val pull = pullChunks args
  fun loop ls = case pull () of
    (false, q) => loop (q :: ls)
  | (true, q) => rev (q :: ls)
  in loop [] end

fun pass2 chunks
  {compile, compilerOut, toplevelOut, progress, error, runtimeExn, mlParseTree} = let

  val queue = ref []
  val chunks = ref $ PolyML.print chunks
  fun readChunk () =
    case !queue of
      s :: rest => (queue := rest; s)
    | [] =>
      case !chunks of
        [] => EOFChunk
      | q :: rest => (queue := q; chunks := rest; readChunk ())

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
        if lo+1 = hi then SOME (String.sub (s, lo)) else read2 ())
  fun getOffset () = case !curToken of
      Reading ((base, reg), lo, _, _) => if reg then base + lo else base
    | EOF pos => pos
  val serial = ref 1
  fun ptFn NONE = ()
    | ptFn (SOME pt) = mlParseTree pt
  fun codeFn NONE () = ()
    | codeFn (SOME code) () = let
      val {fixes, values, structures, signatures, functors, types} = code ()
      fun enter f = app (f PolyML.globalNameSpace)
      in enter #enterFix fixes; enter #enterType types; enter #enterSig signatures;
         enter #enterStruct structures; enter #enterFunct functors; enter #enterVal values end
  (* val print' = print *)
  open PolyML open Compiler
  val parameters = (if compile then [] else noCompile) @ [
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
  (* fun printInput ls =
    case read2 () of
      SOME c => printInput (c :: ls)
    | NONE => (print' $ String.implode (rev ls); ()) *)
  (* fun loop () = printInput [] *)
  in loop () end;

val initialize = pass2 o pass1

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

fun go () = let

fun dropUntil tk s = let
  val lines = String.fields (fn x => x = tk) s
  in String.concatWith (String.str tk) (tl lines) end

fun toString (s: string frag list) = let
  val lines = String.concat (map (fn QUOTE s => dropUntil #")" s | ANTIQUOTE s => s) s)
  in dropUntil #"\n" lines end
(* val periodN = "^periodN" *)
Quote s = toString:
  ALL_TAC
  \\ (ARITH_TAC)
End

(* fun get_binding s = let
  exception Ret of thminfo
  in
    (Theory.upd_binding s (fn i => raise Ret i); NONE)
    handle Ret i => SOME i | HOL_ERR _ => NONE
  end
Theory.current_theory()
get_binding "foo" *)

val _ = HOL_IDE.initialize {
  wrapTactics = true,
  filename = "foo",
  text = "Theorem foo: foo\nProof"^s^"QED\n",
  parseError = fn _ => fn _ => (),
  holParseTree = fn _ => (),
  tacticBlock = fn x => (PolyML.print x; ())
} {
  compile = false,
  compilerOut = fn _ => (),
  error = fn _ => (),
  mlParseTree = fn _ => (),
  progress = fn _ => (),
  runtimeExn = fn _ => (),
  toplevelOut = fn _ => ()
};

(* val foo = TotalDefn.located_qDefine (DB_dtype.mkloc ("foo", 2, true)) "foo" `foo=1` NONE;
Theory.upd_binding "foo" (PolyML.print) ;
Theory.upd_binding "foo" (PolyML.print o DB_dtype.updsrcloc (K (DB_dtype.mkloc ("foo", 1, true))) o PolyML.print) ; *)
in () end;
(*
Timeout.apply (Time.fromMilliseconds 1000) go ();
*)
