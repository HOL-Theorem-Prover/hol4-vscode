(* This structure is renamed to VSCode by the API. Otherwise, you wouldn't be able to use this
extension to edit this file itself. *)
structure VSCodeProto =
struct

val textWidth = ref 100
val printDepth = ref 100

type encode = (string->unit)->unit
fun encodeOut str (print:string->unit) = print str
val encodeJsonInt = encodeOut o Int.toString

local

fun encodeSubstring {str, start, stop} print = let
  fun cleanup start i =
    if start < i then print (String.substring (str, start, i - start)) else ()
  fun hexdigit n = Char.chr (n + (if n < 10 then 48 else 55))
  fun inner start i =
    if i >= stop then cleanup start i
    else
      let val c = String.sub (str, i) in
        if #" " <= c then
          if c = #"\\" then breakStreak start i "\\\\" else
          if c = #"\"" then breakStreak start i "\\\"" else
          inner start (i+1)
        else breakStreak start i (case c of
            #"\b" => "\\b"
          | #"\f" => "\\f"
          | #"\n" => "\\n"
          | #"\r" => "\\r"
          | #"\t" => "\\t"
          | _ => let
            val n = Char.ord c
            in "\\u00" ^ String.implode [hexdigit (n div 16), hexdigit (n mod 16)] end)
      end
  and breakStreak start i next = (cleanup start i; print next; inner (i+1) (i+1))
  in inner start start end

in

fun encodeJsonSubstringContents str = let
  val (str, start, length) = Substring.base str
  in encodeSubstring {str=str, start=start, stop=start+length} end

fun encodeJsonStringContents str =
  encodeSubstring {str=str, start=0, stop=String.size str}

end

fun encodeJsonString str print = (print "\""; encodeJsonStringContents str print; print "\"")

fun encodeJsonSubstring str print = (print "\""; encodeJsonSubstringContents str print; print "\"")

fun encodeJsonArray encode ls print = case ls of
    [] => print "[]"
  | a :: ls => let
    fun inner [] = print "]"
      | inner (a :: ls) = (print ","; encode a print; inner ls)
    val () = print "["
    val () = encode a print
    in inner ls end

fun encodeJsonPair enc1 enc2 (a, b) print =
  ((print "[":unit); (enc1 a print:unit); print ","; (enc2 b print:unit); print "]")

fun encodeJsonPair2 enc = encodeJsonPair enc enc

fun encodeJsonLocation encode ({startPosition,endPosition,...}:PolyML.location) =
  encodeJsonPair2 encode (startPosition, endPosition)

fun printToString encode suff = let
  val buf = ref []
  val () = encode (fn s => buf := s :: !buf)
  in String.concat (List.rev (suff :: !buf)) end

val terminal: PPBackEnd.t = let
  open term_pp_types smpp

  fun add_ssz (s,sz) = let
    val sz = case sz of NONE => UTF8.size s | SOME sz => sz
    in add_stringsz (s, sz) end

  fun wrap enc p =
    add_stringsz (printToString (fn p => (p "\000"; enc p)) "\000", 0) >>
    p >>
    add_stringsz ("\000\000", 0)

  fun colorToHtml Black       = "black"
    | colorToHtml RedBrown    = "maroon"
    | colorToHtml Green       = "green"
    | colorToHtml BrownGreen  = "olive"
    | colorToHtml DarkBlue    = "navy"
    | colorToHtml Purple      = "purple"
    | colorToHtml BlueGreen   = "teal"
    | colorToHtml DarkGrey    = "gray"
    | colorToHtml LightGrey   = "silver"
    | colorToHtml OrangeRed   = "red"
    | colorToHtml VividGreen  = "lime"
    | colorToHtml Yellow      = "yellow"
    | colorToHtml Blue        = "blue"
    | colorToHtml PinkPurple  = "magenta"
    | colorToHtml LightBlue   = "cyan"
    | colorToHtml White       = "white";

  val encodeJsonColor = encodeOut o colorToHtml

  fun encodeJsonStyle s print = case s of
      FG c => (print "{\"FG\":"; encodeJsonColor c print; print "}")
    | BG c => (print "{\"BG\":"; encodeJsonColor c print; print "}")
    | Bold => (print "\"B\"")
    | Underline => (print "\"U\"")
    | UserStyle s => (print "{\"u\":"; encodeJsonString s print; print "}")

  fun add_xstring {s,sz,ann=NONE} = add_ssz (s,sz)
    | add_xstring {s,sz,ann=SOME ann} = let
      val enc = case ann of
          FV _    => encodeOut "\"FV\""
        | BV _    => encodeOut "\"BV\""
        | TyV     => encodeOut "\"TyV\""
        | TyOp _  => encodeOut "\"TyOp\""
        | TySyn _ => encodeOut "\"TySyn\""
        | Const _ => encodeOut "\"Const\""
        | SymConst _ => encodeOut "\"SymConst\""
        | Note s => (fn p => (p "{\"Note\":"; encodeJsonString s p; p "}"))
        | Literal FldName => encodeOut "\"FldName\""
        | Literal StringLit => encodeOut "\"StringLit\""
        | Literal NumLit => encodeOut "\"NumLit\""
        | Literal CharLit => encodeOut "\"CharLit\""
      in wrap enc (add_ssz (s,sz)) end

  in
    {extras = {name = "vscode_terminal", tm_grammar_upd = I, ty_grammar_upd = I},
     add_break = #add_break PPBackEnd.raw_terminal,
     add_newline = #add_newline PPBackEnd.raw_terminal,
     ublock = #ublock PPBackEnd.raw_terminal,
     add_string = add_string,
     add_xstring = add_xstring,
     ustyle = wrap o encodeJsonArray encodeJsonStyle}
  end

fun withPretty f =
  (Parse.current_backend := terminal;
   f () before Parse.current_backend := PPBackEnd.raw_terminal)

fun encodeJsonPretty pp print = let
  fun print' s = encodeJsonStringContents s print
  in print "\""; PolyML.prettyPrint (print', !textWidth) pp; print "\"" end

structure ParseDocDep =
struct

type section = ParseDoc.section

fun encodeJsonMarkup m print = case m of
    ParseDoc.PARA => print "[\"p\"]"
  | ParseDoc.TEXT s => encodeJsonSubstring s print
  | ParseDoc.BRKT s => (print "{\"code\":"; encodeJsonSubstring s print; print "}")
  | ParseDoc.EMPH s => (print "{\"emph\":"; encodeJsonSubstring s print; print "}")
  | ParseDoc.XMPL s => (print "{\"xmpl\":"; encodeJsonSubstring s print; print "}")

fun encodeJsonSection sec print = case sec of
    ParseDoc.TYPE ty => (
    print "{\"kind\":\"type\"";
    print ",\"value\":"; encodeJsonSubstring ty print;
    print "}")
  | ParseDoc.FIELD (header, value) => (
    print "{\"kind\":\"field\"";
    print ",\"header\":"; encodeJsonString header print;
    print ",\"value\":"; encodeJsonArray encodeJsonMarkup value print;
    print "}")
  | ParseDoc.SEEALSO other => (
    print "{\"kind\":\"seeAlso\"";
    print ",\"value\":"; encodeJsonArray encodeJsonSubstring other print;
    print "}")

fun parseFile file = SOME $ ParseDoc.parse_file file handle _ => NONE

end

(* structure ParseDocDep =
struct
type section = unit
fun encodeJsonSection _ _ = raise Bind
fun parseFile _ = NONE
end *)

type parse_data =
  int list * PolyML.parseTree list *
  ((int * int) * (int * int) * Preterm.preterm * Pretype.Env.t) list *
  ((int * int) * HolParser.Simple.decl * (int * int) TacticParser.tac_expr) list
val emptyParseData: parse_data = ([], [], [], [])

val filename = ref ""
val currentThread = ref 0
val currentCompilation =
  ref (NONE : ((parse_data ref * (string * int vector)) * Thread.thread) option)
val lastTrees = ref (emptyParseData, ("", Vector.fromList []))

val printToAsyncChannel = let
  val (suff, printer) = let
    val fd =
      case OS.Process.getEnv "HOLIDE_ASYNC_FD" of
        NONE => raise Bind
      | SOME fd => case SysWord.fromString fd of NONE => raise Bind | SOME fd => fd
    val fd = Posix.FileSys.wordToFD fd
    val _ = Posix.IO.getfd fd
    val w = Posix.IO.mkTextWriter {fd = fd, name = "async_out",
      appendMode = false, initBlkMode = true, chunkSize = 4096}
    val asyncOut = TextIO.mkOutstream $ TextIO.StreamIO.mkOutstream (w, IO.LINE_BUF)
    in ("\000", fn result => (TextIO.output (asyncOut, result); TextIO.flushOut asyncOut))
    end
    handle _ => (
      !WARNING_outstream "<<warning: could not open async stream, printing to stdout>>\n";
      ("\n", print))
  in fn id => fn f =>
    if !currentThread = id then printer $ printToString f suff
    else raise Thread.Interrupt
  end

val lastFailedTactic = ref (NONE: (int*int) option)
fun wrapTactic start (f:'a->'b) stop x =
  f x handle e => (
    if
      case !lastFailedTactic of
        NONE => false
      | SOME (start', stop') => start <= start' andalso stop' <= stop
    then () else lastFailedTactic := SOME (start, stop);
    PolyML.Exception.reraise e)

fun mkLineCounter str = let
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
  in loop 0 [] end

fun partitionPoint len pred = let
  fun loop start len =
    if len = 0 then start
    else let
      val half = len div 2
      val middle = start + half
      in
        if pred middle
        then loop (middle + 1) (len - (half + 1))
        else loop start half
      end
  in loop 0 len end

fun getLineCol lines index = let
  val line = partitionPoint (Vector.length lines) (fn i => Vector.sub (lines, i) <= index)
  in (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1))) end

fun fromLineCol lines (line, col) =
  if line = 0 then col else Vector.sub (lines, line - 1) + col

fun encodeJsonPosLC lines = encodeJsonPair2 encodeJsonInt o getLineCol lines
val encodeJsonPos2LC = encodeJsonPair2 o encodeJsonPosLC
val encodeJsonLocLC = encodeJsonLocation o encodeJsonPosLC

fun holdep text =
  encodeJsonArray encodeJsonString (VSCodeBase.holdep text) print

fun exceptionMessage (exn: exn) =
  PolyML.PrettyBlock(0, false, [], [
    PolyML.PrettyBlock(0, false, [], [PolyML.PrettyString "Exception"]),
    PolyML.PrettyBreak(1, 3),
    PolyML.prettyRepresentation(exn, !printDepth),
    PolyML.PrettyBreak(1, 3),
    PolyML.PrettyString "raised"])

fun get_locn (locn.Loc_Near loc) = get_locn loc
  | get_locn (locn.Loc (locn.LocA start, locn.LocA (l,c))) = SOME (start, (l,c+1))
  | get_locn _ = NONE

val _ = Listener.add_listener Preterm.typecheck_listener ("vscode", fn (ptm, env) =>
  case !currentCompilation of
    SOME ((trees, _), _) =>
    (case get_locn (Preterm.locn ptm) of
      SOME (start, stop) =>
      (case !trees of (p, ts, qs, ds) => trees := (p, ts, (start, stop, ptm, env) :: qs, ds))
    | _ => ())
  | _ => ())
  handle Listener.DUP _ =>
    !WARNING_outstream "<<warning: failed to add typecheck listener>>\n"

fun setFileContents text = let
  val () = case !currentCompilation of
      SOME ((trees, text), thread) => (
      Thread.interrupt thread;
      currentCompilation := NONE;
      case !trees of (_, [], _, _) => () | trees => lastTrees := (trees, text))
    | NONE => ()
  val lines = mkLineCounter text
  val trees = ref emptyParseData
  fun compileThread id = let
    fun printError hard pos msg = printToAsyncChannel id (fn print => (
      print "{\"kind\":\"error\"";
      print ",\"hard\":"; print (if hard then "true" else "false");
      print ",\"pos\":"; encodeJsonPos2LC lines pos print;
      print ",\"msg\":"; encodeJsonPretty msg print;
      print "}"))
    open HolParser.Simple
    val lastHolTree = ref (HolParser.Simple.Chunk 0)
    (* fun addq q = case !trees of (p, ts, qs) => trees := (p, ts, q :: qs) *)
    val _ = PolyML.print_depth 100
    val _ = HOL_IDE.initialize {
      wrapTactics = false,
      filename = !filename,
      text = text,
      parseError = fn pos => fn s => printToAsyncChannel id (fn print => (
        print "{\"kind\":\"error\",\"hard\":true";
        print ",\"pos\":"; encodeJsonPos2LC lines pos print;
        print ",\"msg\":"; encodeJsonString s print;
        print "}")),
      holParseTree = fn t => lastHolTree := t,
      tacticBlock = fn (start, stop, t) =>
        case !trees of (p, ts, qs, ds) =>
          trees := (p, ts, qs, ((start, stop), !lastHolTree, t) :: ds)
    } {
      compile = true,
      compilerOut = fn s => printToAsyncChannel id (fn print => (
        print "{\"kind\":\"compilerOut\"";
        print ",\"body\":"; encodeJsonString s print;
        print "}")),
      toplevelOut = fn s => printToAsyncChannel id (fn print => (
        print "{\"kind\":\"toplevelOut\"";
        print ",\"body\":"; encodeJsonString s print;
        print "}")),
      progress = fn i => printToAsyncChannel id (fn print => (
        case !trees of (cks, ts, qs, ds) => trees := (i :: cks, ts, qs, ds);
        print "{\"kind\":\"compileProgress\"";
        print ",\"pos\":"; encodeJsonPosLC lines i print;
        print "}")),
      error = fn {hard, location = {startPosition, endPosition, ...}, message, ...} =>
        printError hard (startPosition, endPosition) message,
      runtimeExn = fn e =>
        printError true
          (case PolyML.Exception.exceptionLocation e of
            NONE => (case #1 (!trees) of [] => (0,0) | i::_ => (i,i))
          | SOME {startPosition, endPosition, ...} => (startPosition, endPosition))
          (exceptionMessage e),
      mlParseTree = fn t => case !trees of (p, ts, qs, ds) => trees := (p, t :: ts, qs, ds)
    }
    val _ = lastTrees := (!trees, (text, lines))
    val _ = currentCompilation := NONE
    in printToAsyncChannel id (fn print => print "{\"kind\":\"compileCompleted\"}") end
  val compileThread = fn () => let
    val id = !currentThread + 1
    val () = currentThread := id
    val _ = compileThread id handle Thread.Interrupt =>
      printToAsyncChannel id (fn print => print "{\"kind\":\"interrupted\"}")
    in () end
  val thread = Thread.fork (compileThread, [Thread.InterruptState Thread.InterruptDefer])
  in currentCompilation := SOME ((trees, (text, lines)), thread) end

val toLower = String.implode o map Char.toLower o String.explode

fun splitOn c s = let
  fun loop i j out =
    if i = 0 then String.substring (s, i, j - i) :: out
    else let
      val i' = i - 1
      in
        if c = String.sub (s, i')
        then loop i' i' (String.substring (s, i, j - i) :: out)
        else loop i' j out
      end
  val sz = String.size s
  in loop sz sz [] end

fun lastIndexOf' c s i =
  if i = 0 then ~1 else let
    val i' = i - 1
    in if c = String.sub (s, i') then i' else lastIndexOf' c s i' end

fun lastIndexOf c s = lastIndexOf' c s (String.size s)

datatype doc
  = DocText of string
  | DocDoc of ParseDocDep.section list

datatype hover
  = TypeHover of PolyML.location * PolyML.pretty
  | HolTermHover of (int * int) * (int * int) * PolyML.pretty
  | DocHover of doc

fun encodeJsonHover lines hover print = case hover of
    TypeHover (loc, value) => (
    print "{\"kind\":\"type\"";
    print ",\"pos\":"; encodeJsonLocLC lines loc print;
    print ",\"value\":"; encodeJsonPretty value print;
    print "}")
  | HolTermHover (start, stop, value) => (
    print "{\"kind\":\"type\"";
    print ",\"pos\":"; encodeJsonPair2 (encodeJsonPair2 encodeJsonInt) (start, stop) print;
    print ",\"value\":"; encodeJsonPretty value print;
    print "}")
  | DocHover (DocText text) => (
    print "{\"kind\":\"doctxt\"";
    print ",\"text\":"; encodeJsonString text print;
    print "}")
  | DocHover (DocDoc secs) => (
    print "{\"kind\":\"doc\"";
    print ",\"doc\":"; encodeJsonArray ParseDocDep.encodeJsonSection secs print;
    print "}")

val helpDbs = ref []
fun rebuildHelp () = helpDbs := map (fn x => (x, Database.readbase x)) (!Help.indexfiles)
val _ = rebuildHelp ()

fun joinDirFile dir file =
  if dir <> "" andalso String.sub(dir, String.size dir - 1) = #"/" then dir ^ file
  else dir ^ "/" ^ file

fun endsWith suff haystack = let
  val m = String.size suff
  val n = String.size haystack
  in m <= n andalso String.extract (haystack, n - m, NONE) = suff end

fun readToString file = let
  val istr = TextIO.openIn file
  in TextIO.inputAll istr before TextIO.closeIn istr end

fun getDoc file = let
  val docfile = if endsWith ".txt" file then
    SOME (String.substring (file, 0, String.size file - 4) ^ ".doc")
  else NONE
  fun get dir = let
    val doc = case docfile of
        NONE => NONE
      | SOME doc => Option.map DocDoc $ ParseDocDep.parseFile $ joinDirFile dir doc
    val doc = case doc of
        NONE => (SOME $ DocText $ readToString $ joinDirFile dir file handle _ => NONE)
      | doc => doc
    in doc end
  fun loop [] = NONE
    | loop (dir::ds) = case get dir handle _ => NONE of NONE => loop ds | doc => doc
  in loop (!Help.helpdirs) end

fun helpLookup id validate = let
  val sought = toLower id
  fun build1 [] out = out
    | build1 ({comp = Database.Term (fullName, SOME "HOL"), file, ...} :: es) out =
      (case splitOn #"." fullName of
        [] => build1 es out
      | hd :: tl => let
        val ok = if tl = [] then hd = id else (last tl = id andalso validate hd)
        val doc = if ok then getDoc file else NONE
        val out = case doc of NONE => out | SOME doc => DocHover doc :: out
        in build1 es out end)
    | build1 ((_:Database.entry) :: es) out = build1 es out
  exception Rebuild
  fun build [] [] out = out
    | build ((x,db)::xs) (y::ys) out =
      if x = y then build xs ys (build1 (Database.lookup (db, sought)) out) else raise Rebuild
    | build _ _ _ = raise Rebuild
  fun loop () =
    rev (build (!helpDbs) (!Help.indexfiles) [])
    handle Rebuild => (rebuildHelp (); loop ())
  in loop () end

datatype preterm_or_pretype = PTM of Preterm.preterm list * Preterm.preterm | PTY of Pretype.pretype

local
  fun leLC (l,c) (l',c') = l <= l' andalso (l <> l' orelse c <= c')
  fun fixup a NONE = a
    | fixup a (SOME b) = if #1 a = #1 b then a else b
  fun dest_near (locn.Loc_Near loc) = dest_near loc
    | dest_near loc = loc
in
  fun navigateTo' startTarget endTarget = let
    fun navigateToTy ty fail =
      case get_locn locn.Loc_Unknown of (* FIXME Pretype.locn ty *)
        SOME (start, stop) =>
        if leLC start startTarget andalso leLC endTarget stop then
          SOME (navigateToTyCore (start, stop) ty)
        else fail ()
      | _ => fail ()
    and navigateToTys [] fail = fail ()
      | navigateToTys (ty::tys) fail = navigateToTy ty (fn () => navigateToTys tys fail)
    and navigateToTyCore pos ty =
      fixup (pos, PTY ty) (case ty of
        Pretype.Tyop {Args,...} => navigateToTys Args (fn () => NONE)
      | _ => NONE)
    fun navigateTo ls a fail =
      case get_locn (Preterm.locn a) of
        SOME (start, stop) =>
        if leLC start startTarget andalso leLC endTarget stop then
          SOME (navigateToCore (start, stop) ls a)
        else fail ()
      | _ => fail ()
    and navigateToCore pos ls a =
      fixup (pos, PTM (ls, a)) (case a of
        Preterm.Var {Ty, ...} => navigateToTy Ty (fn () => NONE)
      | Preterm.Const {Ty, ...} => navigateToTy Ty (fn () => NONE)
      | Preterm.Overloaded {Ty, ...} => navigateToTy Ty (fn () => NONE)
      | Preterm.Comb {Rand, Rator, ...} =>
        navigateTo ls Rand (fn () => navigateTo ls Rator (fn () => NONE))
      | Preterm.Abs {Bvar, Body, ...} =>
        navigateTo ls Bvar (fn () => navigateTo (Bvar::ls) Body (fn () => NONE))
      | Preterm.Constrained {Ptm, Ty, ...} =>
        navigateTo ls Ptm (fn () => navigateToTy Ty (fn () => NONE))
      | Preterm.Antiq _ => NONE
      | Preterm.Pattern {Ptm, ...} => navigateTo ls Ptm (fn () => NONE))
    fun navigateTo' [] = NONE
      | navigateTo' ((start, stop, ptm, env) :: ds) =
        if leLC start startTarget andalso leLC endTarget stop then
          SOME (navigateToCore (start, stop) [] ptm, env)
        else navigateTo' ds
    in navigateTo' end
end

fun getState startTarget endTarget = let
  val state = case !currentCompilation of
      SOME ((ref (stop::_, trees, ds, _), (text, lines)), _) => let
      val offset = fromLineCol lines endTarget
      in if offset <= stop then SOME (text, lines, offset, trees, ds) else NONE end
    | _ => NONE
  val state = case (state, !lastTrees) of
      (NONE, ((stop::_, trees, ds, _), (text, lines))) => let
      val offset = fromLineCol lines endTarget
      in if offset <= stop then SOME (text, lines, offset, trees, ds) else NONE end
    | (state, _) => state
  in
    case state of
      NONE => NONE
    | SOME (text, lines, endOffset, trees, ds) => let
      val offset = {startOffset = fromLineCol lines startTarget, endOffset = endOffset}
      val ds = (navigateTo' startTarget endTarget ds)
      val pt = HOL_IDE.navigateTo' trees offset
      in SOME (text, lines, offset, trees, ds, pt) end
  end

fun getBinding s = let
  exception Ret of thminfo
  in
    (Theory.upd_binding s (fn i => raise Ret i); NONE)
    handle Ret i => SOME i | HOL_ERR _ => NONE
  end

fun lookupThmInfo kn =
  if #Thy kn = Theory.current_theory () then
    case getBinding (#Name kn) of
      SOME i => SOME i
    | NONE => Option.map snd (DB.lookup kn)
  else Option.map snd (DB.lookup kn)

fun getHoverInfo startTarget endTarget =
  case getState startTarget endTarget of
    NONE => print "[]"
  | SOME (text, lines, _, trees, tm, pt) => let
    fun process loc props = let
      fun validate str = let
        fun look [] = false
          | look (PolyML.PTstructureAt {file, ...} :: props) = let
            val basename = String.extract (file, lastIndexOf #"/" file + 1, NONE)
            val stem = String.extract (basename, 0, SOME (lastIndexOf #"." basename))
            in str = stem andalso look props end
          | look (_ :: props) = look props
        in look props end
      fun fromProps [] out = out
        | fromProps (PolyML.PTtype ty :: props) (isId, _) = fromProps props (isId, SOME ty)
        | fromProps (PolyML.PTrefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (PolyML.PTdefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (_ :: props) out = fromProps props out
      val (isId, ty) = fromProps props (NONE, NONE)
      val (id, value, help) = case isId of
          NONE => (NONE, NONE, [])
        | SOME i => let
          val {startPosition, endPosition, ...} = loc
          val id = String.substring (text, startPosition, endPosition - startPosition)
          val help =
            if lastIndexOf #"." id < 0 then let
              fun validate str = let
                fun look [] = false
                  | look (PolyML.PTstructureAt {file, ...} :: props) = let
                    val basename = String.extract (file, lastIndexOf #"/" file + 1, NONE)
                    val stem = String.extract (basename, 0, SOME (lastIndexOf #"." basename))
                    in str = stem orelse look props end
                  | look (_ :: props) = look props
                in look props end
              in helpLookup id validate end
            else let
              val components = splitOn #"." id
              val fst = hd components
              in helpLookup (last components) (fn s => s = fst) end
            handle _ => []
          val isGlobalId = i = 0 orelse let
            fun look [] = NONE
              | look (PolyML.PTdeclaredAt loc :: props) = SOME loc
              | look (_ :: props) = look props
            fun lookRefs [] = false
              | lookRefs (PolyML.PTreferences (exp, loc) :: props) = exp
              | lookRefs (_ :: props) = lookRefs props
            in
              case look props of
                NONE => false
              | SOME {startPosition, endPosition, ...} =>
                case HOL_IDE.navigateTo' trees {startOffset=startPosition, endOffset=endPosition} of
                  NONE => false
                | SOME (_, props) => lookRefs props
            end
          val value = if isGlobalId then #lookupVal PolyML.globalNameSpace id else NONE
          in (SOME id, value, help) end
      open PolyML
      val ty = Option.map (fn ty =>
        NameSpace.Values.printType (ty, !printDepth, SOME globalNameSpace)) ty
      val value = case value of
          NONE => NONE
        | SOME value =>
          case NameSpace.Values.print (value, !printDepth) of
            PrettyString "" => NONE
          | otherwise => SOME otherwise
      val out = case (id, ty, value) of
          (_, NONE, NONE) => []
        | (NONE, SOME ty, NONE) => [TypeHover (loc, ty)]
        | (SOME id, SOME ty, NONE) =>
          [TypeHover (loc, PrettyBlock(0, true, [],
            [PrettyString ("val " ^ id ^ ":"), PrettyBreak(1, 2), ty]))]
        | (id, ty, SOME value) =>
          [TypeHover (loc, PrettyBlock(2, true, [], [
            PrettyBlock(0, false, [],
              (case ty of
                 NONE => [PrettyString ("val " ^ Option.getOpt (id, "_"))]
                | SOME ty => [
                  PrettyString ("val " ^ Option.getOpt (id, "_") ^ ":"),
                  PrettyBreak(1, 2), ty])
              @ [PrettyBreak(1, 2), PrettyString "="]),
             PrettyBreak(1, 0), value]))]
      in help @ out end
    fun fromTree NONE = []
      | fromTree (pt as (SOME (loc, props))) =
        case process loc props of
          [] => fromTree (HOL_IDE.moveUp pt)
        | out => out
    fun fromTerm NONE = fromTree pt
      | fromTerm (SOME ((_, PTY _), _)) = fromTree pt
      | fromTerm (SOME (((start, stop), PTM (_, tm)), env)) =
        case Preterm.typecheck NONE tm env of
          errormonad.Some (_, tm) => let
          val typp = Parse.pp_type_without_colon (type_of tm)
          val _ = Globals.max_print_depth := 4
          val tmpp = Parse.pp_term tm
          val _ = Globals.max_print_depth := ~1
          open PolyML
          val pp = PrettyBlock(0, true, [], [tmpp, PrettyString ":", PrettyBreak(1, 2), typp])
          in [HolTermHover (start, stop, pp)] end
        | _ => fromTree pt
    in withPretty (fn () => encodeJsonArray (encodeJsonHover lines) (fromTerm tm) print) end

fun gotoDefinition target =
  case getState target target of
    SOME (text, lines, _, _, tm, pt) => let
    datatype position
      = PolyLoc of PolyML.location
      | FileLine of string * int option
      | LineCol of (int * int) * (int * int)
    val out = case tm of
        SOME ((loc, PTY ty), env) =>
        (case Pretype.toTypeM ty env of
          errormonad.Some (_, ty) => (let
            val {Thy, Tyop, ...} = Type.dest_thy_type ty
            (* TODO *)
            in [] end
            handle HOL_ERR _ => [])
        | _ => [])
      | SOME ((loc, PTM (bvs, tm)), env) =>
        (case Preterm.typecheck NONE tm env of
          errormonad.Some (_, tm) => (let
            val (hd, _) = strip_comb tm
            fun findVar [] = []
              | findVar (bv::bvs) =
                case Preterm.typecheck NONE bv env of
                  errormonad.Some (_, tm) => if term_eq tm hd then
                    case get_locn (Preterm.locn bv) of
                      SOME tgt => [(LineCol loc, LineCol tgt)]
                    | _ => []
                  else findVar bvs
                | _ => findVar bvs
            in
              if is_var hd then
                findVar bvs
              else if is_const hd then
                case DefnBase.lookup_userdef hd of
                  SOME {thmname,...} => (case lookupThmInfo thmname of
                    SOME {loc = DB.Located {scriptpath, linenum, ...}, ...} =>
                    [(LineCol loc,
                      FileLine (holpathdb.subst_pathvars scriptpath, SOME (linenum - 1)))]
                  | _ => [])
                | NONE => []
              else []
            end
            handle HOL_ERR _ => [])
        | _ => [])
      | _ => []
    fun fromProps [] r = r
      | fromProps (PolyML.PTdeclaredAt loc :: rest) (file, ty, _) = (file, ty, SOME loc)
      | fromProps (PolyML.PTstructureAt {file,...} :: props) (_, ty, df) =
        fromProps props (SOME file, ty, df)
      | fromProps (PolyML.PTtype ty :: props) (file, _, df) = fromProps props (file, SOME ty, df)
      | fromProps (_ :: props) r = fromProps props r
    val out =
      case (out, pt) of
        ([], SOME (origin, props)) =>
        (case fromProps props (NONE, NONE, NONE) of
          (_, _, NONE) => []
        | (file, ty, SOME loc) => let
          val newLoc = case (file, ty) of
            (SOME file, SOME _) => let
            val {startPosition, endPosition, ...} = origin
            val id = String.substring (text, startPosition, endPosition - startPosition)
            val basename = String.extract (file, lastIndexOf #"/" file + 1, NONE)
            val stem = String.extract (basename, 0, SOME (lastIndexOf #"." basename))
            in
              if 6 <= size stem andalso String.extract (stem, size stem - 6, NONE) = "Theory" then
                case lookupThmInfo
                    {Name = id, Thy = String.extract (stem, 0, SOME (size stem - 6))} of
                  SOME {loc = DB.Located {scriptpath, linenum, ...}, ...} =>
                  FileLine (holpathdb.subst_pathvars scriptpath, SOME (linenum - 1))
                | _ => PolyLoc loc
              else PolyLoc loc
            end
          | _ => PolyLoc loc
          in [(PolyLoc origin, newLoc)] end)
      | _ => out
    fun encodeJsonFileLine (file, startLine) print = (
      print "{\"file\":"; encodeJsonString file print;
      case startLine of
        SOME n => (print ",\"line\":"; encodeJsonInt n print)
      | NONE => ();
      print "}")
    val encodeJsonPosition = fn
      PolyLoc (loc as {file, startLine, ...}) =>
        if file = "" then encodeJsonLocLC lines loc
        else encodeJsonFileLine (file, SOME (startLine - 1))
      | FileLine fileLine => encodeJsonFileLine fileLine
      | LineCol range => encodeJsonPair2 (encodeJsonPair2 encodeJsonInt) range
    in encodeJsonArray (encodeJsonPair2 encodeJsonPosition) out print end
  | _ => print "[]"

fun selectTacticSeq startTarget endTarget = let
  val state = case !currentCompilation of
    SOME ((ref (_, _, _, ds as ((_, stop), _, _) :: _), (text, lines)), _) => let
    val offset = fromLineCol lines endTarget
    in if offset <= stop then SOME (text, lines, ds) else NONE end
  | _ => NONE
  val (text, lines, ds) = case state of
    NONE => let
    val ((_, _, _, ds), (text, lines)) = !lastTrees
    in (text, lines, ds) end
  | SOME state => state
  val startOffset = fromLineCol lines startTarget
  val endOffset = fromLineCol lines startTarget
  open TacticParser
  fun build sp e = let
    val ls = sliceTacticBlock startOffset endOffset false sp e
    in if List.all null ls then NONE else SOME (printFragsAsE text ls) end
  fun findProof [] = NONE
    | findProof (((start, stop), decl, tree) :: ds) =
      if start > startOffset then findProof ds else
      if stop < endOffset then NONE else build (start, stop) tree
  val _ = case findProof ds of
    NONE => print "null"
  | SOME s => encodeJsonString s print
  in () end

end;
