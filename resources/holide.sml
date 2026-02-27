val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLAst.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLAst.sml";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLParser.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLParser.sml";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLToSML.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLToSML.sml";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLPrinter.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HOLPrinter.sml";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HolParser.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HolParser.sml";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HolParserOld.sig";
val _ = use "/home/mario/HOL4-stable/tools/Holmake/HolParserOld.sml";
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

datatype props =
  PQuote
| PPrint of string
| PThy of string
| PIdContent of string
| PDeclaredAt of {file: string, startLine: int, endLine: int, startPosition: int, endPosition: int}
| PType of PolyML.NameSpace.Values.typeExpression
| POther of PolyML.ptProperties

datatype built = Built of (FixedInt.int * FixedInt.int) * props list * built list

val initialize: bool ->
  { text: string,
    filename: string,
    parseError: int * int -> string -> unit,
    compilerOut: string -> unit,
    toplevelOut: string -> unit,
    progress: int -> unit,
    error: error -> unit,
    runtimeExn: exn -> unit,
    mlParseTreeOld: PolyML.parseTree -> unit,
    mlParseTree: built -> unit,
    holParseTreeOld: HolParserOld.Simple.decl -> unit,
    holParseTree: HOLAst.dec -> unit
  } -> unit

val moveUp: subtree -> subtree
val moveDown: subtree -> subtree
val moveLeft: subtree -> subtree
val moveRight: subtree -> subtree
val printTree: FixedInt.int -> subtree -> PolyML.pretty option
val navigateTo: subtree -> {startOffset: FixedInt.int, endOffset: FixedInt.int} -> subtree
val navigateTo': trees -> {startOffset: FixedInt.int, endOffset: FixedInt.int} -> subtree

val at: PolyML.parseTree list -> int list -> subtree

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
  fun f (t, _) = mk_oracle_thm "fast_proof" t
  fun f2 g = (
    if current_theory () = "scratch"
    then HOL_WARNING "HOL_IDE" "prove" "calling prove before new_theory"
    else Tactical.set_prover f;
    f g)
  in Tactical.set_prover f2 end

fun postPrelude () = ()

val compile = ref true

datatype props =
  PQuote
| PPrint of string
| PThy of string
| PIdContent of string
| PDeclaredAt of {file: string, startLine: int, endLine: int, startPosition: int, endPosition: int}
| PType of PolyML.NameSpace.Values.typeExpression
| POther of PolyML.ptProperties

datatype built = Built of (FixedInt.int * FixedInt.int) * props list * built list

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

fun prettyToString pp = let
  val ss = ref []
  val _ = PolyML.prettyPrint (fn s => ss := s :: !ss, 100) pp
  in concat (rev (!ss)) end

fun trProps [] = []
  | trProps (PolyML.PTprint p :: ls) = PPrint (prettyToString (p 5)) :: trProps ls
  | trProps (PolyML.PTdeclaredAt p :: ls) = PDeclaredAt p :: trProps ls
  | trProps (PolyML.PTtype t :: ls) = PType t :: trProps ls
  | trProps (PolyML.PTparent _ :: ls) = trProps ls
  | trProps (PolyML.PTfirstChild _ :: ls) = trProps ls
  | trProps (PolyML.PTpreviousSibling _ :: ls) = trProps ls
  | trProps (PolyML.PTnextSibling _ :: ls) = trProps ls
  (* | trProps (x :: ls) = POther x :: trProps ls *)
  | trProps (x :: ls) = trProps ls

fun addProps pr (Built (p, pr', ls)) = Built (p, pr @ pr', ls)

fun build (tree as ({startPosition, endPosition, ...}, props)) =
  Built ((startPosition, endPosition), trProps props, buildList (moveDown (SOME tree)))

and buildList NONE = []
  | buildList (tree as SOME t) = build t :: buildList (moveRight tree)

fun build0 ({startPosition, endPosition, ...}, props) =
  Built ((startPosition, endPosition), trProps props, [])

datatype toppt = PTTop of PolyML.parseTree option list | PTInner of PolyML.parseTree option

fun topHead (PTInner pt) = pt
  | topHead (PTTop []) = NONE
  | topHead (PTTop (pt::_)) = pt

fun topAsInner (PTInner pt) = pt
  | topAsInner _ = raise Bind

fun moveTopDown (PTInner pt) = moveDown pt
  | moveTopDown (PTTop []) = NONE
  | moveTopDown (PTTop (pt::_)) = moveDown pt

fun moveTopRight (PTInner pt) = PTInner (moveRight pt)
  | moveTopRight (PTTop []) = PTTop []
  | moveTopRight (PTTop (pt::pts)) = PTTop (moveRight pt :: pts)

fun moveTopSemi (PTInner pt) = PTInner pt
  | moveTopSemi (PTTop []) = PTTop []
  | moveTopSemi (PTTop (_::pts)) = PTTop pts

local open HOLAst in

fun overspan sp (b as Built (sp', props, _)) =
  if sp = sp' then b else Built (sp, props, [b])

fun mkList [a] = a
  | mkList ls = let
    val Built ((a,_),_,_) = hd ls
    val Built ((_,b),_,_) = last ls
    in Built ((a,b), [], ls) end

fun respan sp (Built (_, props, ls)) = Built (sp, props, ls)

fun withSpan sp NONE = Built (sp, [], [])
  | withSpan sp (SOME pt) = respan sp (build0 pt)

fun withProps sp NONE ls = Built (sp, [], ls)
  | withProps sp (SOME tree) ls = Built (sp, trProps (#2 tree), ls)

fun onList _ [] pt acc = (acc, pt)
  | onList f (x::xs) pt acc = onList f xs (moveRight pt) (f (x, pt, acc))

fun skipDecs [] pt = pt
  | skipDecs (DecExpansion {result, ...} :: ds) pt = skipDecs ds (skipDecs result pt)
  | skipDecs (DecSemi _ :: ds) pt = skipDecs ds (moveTopSemi pt)
  | skipDecs (_ :: ds) pt = skipDecs ds (moveTopRight pt)

fun annotateId id pt = addProps [PIdContent (#2 id)] (withProps (idSpan id) pt [])

fun annotateTy ty pt = withProps (tySpan ty) pt (case ty of
    TyVar _ => []
  | TyRecord {elems = {args, ...}, ...} =>
    rev (#1 (onList (fn ({lab,ty,...},pt,acc) => let
      val pt = moveDown pt
      val lab = case lab of NONE => [] | SOME id => [annotateId id pt]
      val ty = annotateTy ty (moveRight pt)
      in mkList (lab @ [ty]) :: acc end) args (moveDown pt) []))
  | TyTuple {args, ...} => rev (#1 (onList (fn (ty,pt,acc) =>
    annotateTy ty pt :: acc) args (moveDown pt) []))
  | TyCon {args = Empty, ...} => []
  | TyCon {args = One t1, id} =>
    (case moveDown pt of pt => [annotateTy t1 pt, annotateId id (moveRight pt)])
  | TyCon {args = Many {elems = {args, ...}, ...}, id} =>
    (case moveDown pt of pt =>
      rev (annotateId id (moveRight pt) ::
        #1 (onList (fn (ty, pt, acc) => annotateTy ty pt :: acc) args (moveDown pt) [])))
  | TyArrow {from, to, ...} =>
    (case moveDown pt of pt => [annotateTy from pt, annotateTy to (moveRight pt)])
  | TyParens {ty, ...} => [annotateTy ty pt]
  | BadTy _ => [])

fun annotateTybind {tycon, bind, ...} pt = let
  val pt = moveDown pt
  val bind = case bind of NONE => [] | SOME {ty, ...} => [annotateTy ty (moveRight pt)]
  in mkList (annotateId tycon pt :: bind) end

fun annotateTybinds {args, ...} =
  onList (fn (tybind, pt, acc) => annotateTybind tybind pt :: acc) args

fun annotateDatatype {args, ...} withtype_ pt = let
    val (acc, pt) = onList (fn ({tycon, rhs, ...}, pt, acc) => let
      val pt = moveDown pt
      val tycon = annotateId tycon pt
      val rhs = case rhs of
        DatvalElems ls =>
        mkList (rev (#1 (onList (fn ({id, arg, ...}, pt, acc) => let
          val pt = moveDown pt
          val id = annotateId id pt
          val ty = case arg of
            NONE => []
          | SOME {ty, ...} => [annotateTy ty NONE] (* FIXME: PolyML bug *)
          in mkList (id :: ty) :: acc end) ls (moveDown (moveRight pt)) [])))
      | DatvalDatatype {id, ...} => annotateId id (moveRight pt) (* FIXME: PolyML bug *)
      in mkList [tycon, rhs] :: acc end) args pt []
    in
      case withtype_ of
        NONE => (acc, pt)
      | SOME {tybind, ...} => annotateTybinds tybind pt acc
    end

fun annotateExp _ (ExpExpansion {orig, result}) pt =
    overspan (expSpan orig) (annotateExp (SOME orig) result pt)
  | annotateExp (SOME (IfThenElse {else_ = NONE, ...})) (e as IfThenElse {exp1, exp2, ...}) pt =
    withProps (expSpan e) pt (case moveDown pt of pt =>
      [annotateExp NONE exp1 pt, annotateExp NONE exp2 (moveRight pt)])
  | annotateExp (SOME (HOLFullQuote _)) (App (_, e)) pt =
    addProps [PQuote] (withProps (expSpan e) pt (
      rev (annotateQuote e (moveRight (moveDown pt)) [])))
  | annotateExp (SOME (HOLQuote _)) e pt =
    addProps [PQuote] (withProps (expSpan e) pt (rev (annotateQuote e pt [])))
  | annotateExp _ (Ident {op_ = NONE, id}) pt = annotateId id pt
  | annotateExp sp e pt =
    (PolyML.print (sp, e, Option.map build pt);
    withProps (expSpan e) pt (case e of
      Wild _ => []
    | IntegerConstant _ => []
    | WordConstant _ => []
    | StringConstant _ => []
    | CharConstant _ => []
    | RealConstant _ => []
    | Unit _ => []
    | Ident {op_ = NONE, ...} => raise Fail "unreachable"
    | Ident {op_ = SOME _, id} => [annotateId id pt]
    | List {elems = {args, ...}, ...} =>
      rev (#1 (onList (fn (e, pt, acc) => annotateExp NONE e pt :: acc) args (moveDown pt) []))
    | Tuple {elems = {args, ...}, ...} =>
      rev (#1 (onList (fn (e, pt, acc) => annotateExp NONE e pt :: acc) args (moveDown pt) []))
    | Record {elems = {args, ...}, ...} =>
      rev (#1 (onList (annotateRow NONE) args (moveDown pt) []))
    | Parens {exp, ...} => [annotateExp NONE exp pt]
    | Infix {left, id, right} => let
      val pt = moveDown pt
      val left = annotateExp NONE left pt; val pt = moveRight pt
      in [left, annotateId id pt, annotateExp NONE right (moveRight pt)] end
    | Typed {exp, ty, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE exp pt, annotateTy ty (moveRight pt)] end
    | Layered {op_, id, ty, pat, ...} => let
      val pt = moveDown pt
      fun var pt = let
        val sp = idSpan id
        val e = addProps [PIdContent (#2 id)] (withSpan sp pt)
        in case op_ of NONE => e | SOME p => withProps (p, #2 sp) pt [e] end
      val e = case ty of
        NONE => var pt
      | SOME {ty, ...} => let
        val pt1 = moveDown pt
        val v as Built ((a,_),_,_) = var pt1
        val ty as Built ((_,b),_,_) = annotateTy ty (moveRight pt1)
        in withProps (a, b) pt [v, ty] end
      in [e, annotateExp NONE pat (moveRight pt)] end
    | Or _ => raise Fail "unexpanded or pattern"
    | Select _ => []
    | Sequence {elems = {args, ...}, ...} =>
      rev (#1 (onList (fn (e, pt, acc) => annotateExp NONE e pt :: acc) args (moveDown pt) []))
    | LetInEnd {dec, exps = {args, ...}, ...} => let
      val (acc, pt) = annotateDecs dec (PTInner (moveDown pt)) []
      fun f (e, pt, acc) = annotateExp NONE e pt :: acc
      in rev (#1 (onList f args (topAsInner pt) acc)) end
    | App (f, x) => let
      val pt = moveDown pt
      in [annotateExp NONE f pt, annotateExp NONE x (moveRight pt)] end
    | AndAlso {left, right, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE left pt, annotateExp NONE right (moveRight pt)] end
    | OrElse {left, right, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE left pt, annotateExp NONE right (moveRight pt)] end
    | Handle {exp, elems, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE exp pt, mkList (annotateArms elems (moveRight pt))] end
    | Raise {exp, ...} => [annotateExp NONE exp (moveDown pt)]
    | IfThenElse {exp1, exp2, else_, ...} => let
      val pt = moveDown pt; val exp1 = annotateExp NONE exp1 pt
      val pt = moveRight pt; val exp2 = annotateExp NONE exp2 pt
      val r = case else_ of
        NONE => [exp1, exp2]
      | SOME {exp3, ...} => [exp1, exp2, annotateExp NONE exp3 (moveRight pt)]
      in r end
    | While {exp1, exp2, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE exp1 pt, annotateExp NONE exp2 (moveRight pt)] end
    | Case {exp, elems, ...} => let
      val pt = moveDown pt
      in [annotateExp NONE exp pt, mkList (annotateArms elems (moveRight pt))] end
    | Fn {elems, ...} => annotateArms elems pt
    | HOLFullQuote _      => raise Fail "unexpanded HOL syntax"
    | HOLQuote _          => raise Fail "unexpanded HOL syntax"
    | HOLLinePragma _     => raise Fail "unexpanded HOL syntax"
    | HOLLinePragmaWith _ => raise Fail "unexpanded HOL syntax"
    | HOLFilePragma _     => raise Fail "unexpanded HOL syntax"
    | HOLFilePragmaWith _ => raise Fail "unexpanded HOL syntax"
    | ExpEmpty _          => []
    | ExpBad _            => []
    | ExpExpansion _      => raise Fail "unreachable"))

and annotateRow (x as SOME (LabAs {ty, aspat, ...})) (y as LabEq {lab, exp, ...}, pt, acc) = let
    val _ = PolyML.print (x, y, Option.map build pt)
    val pt = moveDown pt
    val pt1 = moveRight pt
    val (exp, ty) = case (ty, exp) of
      (SOME _, Typed {exp, ty, ...}) => let
      val pt1 = moveDown pt1
      in (annotateExp NONE exp pt1, fn e => mkList [e, annotateTy ty (moveRight pt1)]) end
    | _ => (annotateExp NONE exp pt1, fn e => e)
    val r = case aspat of
      NONE => ty exp
    | SOME _ => mkList [ty (annotateId lab pt), exp]
    in r :: acc end
  | annotateRow _ (r, pt, acc) = case r of
      DotDotDot _ => acc
    | LabEq {lab, exp, ...} => let
      val pt = moveDown pt
      in mkList [annotateId lab pt, annotateExp NONE exp (moveRight pt)] :: acc end
    | LabAs {id, ty = NONE, aspat = NONE} => annotateId id pt :: acc
    | LabAs {id, ty, aspat} => let
      fun eid pt = annotateId id pt
      fun ety pt = case ty of
        NONE => eid pt
      | SOME {ty, ...} => case moveDown pt of pt =>
        mkList [eid pt, annotateTy ty (moveRight pt)]
      val e = case aspat of
        NONE => ety pt
      | SOME {exp, ...} => case moveDown pt of pt =>
        mkList [ety pt, annotateExp NONE exp (moveRight pt)]
      in e :: acc end
    | LabExpansion {orig, result} => annotateRow (SOME orig) (result, pt, acc)

and annotateArms arms pt =
  (PolyML.print (arms, Option.map build pt);
  rev (#1 (onList (fn ({pat, exp, ...}, pt, acc) =>
    case moveDown pt of pt =>
    mkList [annotateExp NONE pat pt, annotateExp NONE exp (moveRight pt)] :: acc
  ) arms (moveDown pt) [])))

and annotateQuote (List {elems = {args, ...}, ...}) pt acc = let
    fun go [] _ acc = acc
      | go (e :: es) pt acc =
        go es (moveRight pt) (case e of
          App (Ident {id = (_, "ANTIQUOTE"), ...}, e) =>
          annotateExp NONE e (moveRight (moveDown pt)) :: acc
        | _ => acc)
    in go args (moveDown pt) acc end
  | annotateQuote _ _ acc = acc

and annotateFunPat (App (f, x)) pt = let
    val (pt, f) = annotateFunPat f pt
    val x = annotateExp NONE x pt
    in (moveRight pt, mkList [f, x]) end
  | annotateFunPat (e as Parens {exp, ...}) pt = let
    val (pt, e') = annotateFunPat exp pt
    in (pt, overspan (expSpan e) e') end
  | annotateFunPat (Infix {left, id, right}) pt = let
    val f = annotateId id pt
    val pt = moveRight pt
    val pt1 = moveDown pt
    val left = annotateExp NONE left pt1
    val right = annotateExp NONE right (moveRight pt1)
    in (moveRight pt, mkList [left, f, right]) end
  | annotateFunPat e pt = (moveRight pt, annotateExp NONE e pt)

and annotateDecs [] pt acc = (acc, pt)
  | annotateDecs (DecExpansion {result = [], ...} :: ds) pt acc = annotateDecs ds pt acc
  | annotateDecs (d::ds) pt acc = case annotateDec d pt of (d, pt) => annotateDecs ds pt (d::acc)

and annotateDec (DecExpansion {orig = DecExp _,
      result = [DecVal {elems = {args = [{eq = SOME {exp,...},...}],...},...}]}) pt =
    (annotateExp NONE exp (moveRight (moveDown (moveTopDown pt))), moveTopRight pt)
  | annotateDec (DecExpansion {orig as HOLTheory {id, attrs, elems, ...}, result}) pt = let
    val acc = [addProps [PThy (#2 id)] (annotateId id NONE)]
    val bare = List.exists (fn {key = (_, "bare"), bind = NONE} => true | _ => false)
      (case attrs of NONE => [] | SOME v => #args (#attrs v))
    fun collect [] pt acc = (acc, pt)
      | collect (DecOpen {elems, ...} :: decs) pt (opens, strs) = let
        val (opens, _) = onList (fn (id, pt, acc) => (id, pt) :: acc) elems (moveTopDown pt) opens
        in collect decs (moveTopRight pt) (opens, strs) end
      | collect (DecLocal {dec1, dec2, ...} :: decs) pt acc = let
        val (acc, pt) = collect dec1 (PTInner (moveTopDown pt)) acc
        in collect decs (moveTopRight pt) (#1 (collect dec2 pt acc)) end
      | collect (DecSemi _ :: decs) pt acc = collect decs (moveTopSemi pt) acc
      | collect (DecStructure {elems = {args = [{id, ...}], ...}, ...} :: decs)
          pt (opens, strs) =
        collect decs (moveTopRight pt) (opens, (id, moveDown (moveTopDown pt)) :: strs)
      | collect (_ :: decs) pt acc = collect decs (moveTopRight pt) acc
    val ((opens, strs), pt) = collect result pt ([], [])
    val opens = if bare then opens else let
      fun skipN (s1 :: opens) (skip as (s2 :: rest)) =
          if #2 (#1 s1) = s2 then skipN opens rest else s1 :: skipN opens skip
        | skipN opens [] = opens
        | skipN [] _ = []
      in skipN opens ["Parse", "bossLib", "boolLib", "HolKernel"] end
    fun annot _ [] acc = acc
      | annot isThy ({id, attrs} :: rest) {opens, strs, acc} = let
        val (opens, acc) = case opens of
          (str, pt) :: opens => let
          val t = annotateId str pt
          val t = if isThy then addProps [PThy (#2 id)] t else t
          in (opens, t :: acc) end
        | _ => (opens, acc)
        fun f ({key = (_, "alias"), bind = SOME {vals = [_], ...}}, ((id,pt) :: strs, acc)) =
            (strs, annotateId id pt :: acc)
          | f (_, acc) = acc
        val (strs, acc) = List.foldl f (strs, acc)
          (case attrs of NONE => [] | SOME v => #args (#attrs v))
        in annot isThy rest {opens = opens, strs = strs, acc = acc} end
    fun annotList [] {acc, ...} = acc
      | annotList (HOLAncestors {elems, ...} :: ls) acc = annotList ls (annot true elems acc)
      | annotList (HOLLibs {elems, ...} :: ls) acc = annotList ls (annot false elems acc)
    val acc = annotList elems {opens = rev opens, strs = rev strs, acc = acc}
    in (withProps (decSpan orig) NONE (rev acc), pt) end
  | annotateDec (DecExpansion {orig as HOLDefinition {id, attrs, ...}, result}) pt = let

    in (withProps (decSpan orig) NONE (rev acc), pt) end
  | annotateDec (DecExpansion {orig, result}) pt = let
    val (acc, pt) = annotateDecs result pt []
    in (withProps (decSpan orig) NONE (rev acc), pt) end
  | annotateDec (d as DecSemi _) pt = (withProps (decSpan d) (topHead pt) [], moveTopSemi pt)
  | annotateDec d pt = let
    val _ = PolyML.print (d, Option.map build (topHead pt))
    val children = case d of
      DecSemi _ => raise Fail "unreachable"
    | DecVal {elems = {args, ...}, ...} =>
      #1 (onList (fn ({pat, eq, ...}, pt, acc) => let
        val pt = moveDown pt
        val pat = annotateExp NONE pat pt
        in case eq of
          NONE => pat :: acc
        | SOME {exp, ...} => mkList [pat, annotateExp NONE exp (moveRight pt)] :: acc
        end) args (moveTopDown pt) [])
    | DecFun {fvalbind = {args, ...}, ...} =>
      #1 (onList (fn (ls, pt, acc) =>
        mkList (rev (#1 (onList (fn ({pat, exp, ...}, pt, acc) => let
          val pt = moveDown pt
          val (pt, pat) = annotateFunPat pat pt
          in mkList [pat, annotateExp NONE exp pt] :: acc end
          ) ls (moveDown pt) []))) :: acc
        ) args (moveTopDown pt) [])
    | DecType {tybind, ...} => #1 (annotateTybinds tybind (moveTopDown pt) [])
    | DecEqtype {tybind, ...} => #1 (annotateTybinds tybind (moveTopDown pt) [])
    | DecDatatype {datbind, withtype_, ...} =>
      #1 (annotateDatatype datbind withtype_ (moveTopDown pt))
    | DecAbstype {datbind, withtype_, dec, ...} => let
      val (acc, pt) = annotateDatatype datbind withtype_ (moveTopDown pt)
      in #1 (annotateDecs dec (PTInner pt) acc) end
    | DecException {elems = {args, ...}, ...} =>
      #1 (onList (fn (ex, pt, acc) => (case ex of
          ExnNew {id, arg = NONE, ...} => annotateId id pt
        | ExnNew {id, arg = SOME {ty, ...}, ...} => (case moveDown pt of pt =>
          mkList [annotateId id pt, annotateTy ty (moveRight pt)])
        | ExnReplicate {id, tgt, ...} => (case moveDown pt of pt =>
          mkList [annotateId id pt, annotateId tgt (moveRight pt)]))
        :: acc) args (moveTopDown pt) [])
    | DecLocal {dec1, dec2, ...} => let
      val (acc, pt) = annotateDecs dec1 (PTInner (moveTopDown pt)) []
      in #1 (annotateDecs dec2 pt acc) end
    | DecOpen {elems, ...} =>
      #1 (onList (fn (id, pt, acc) => annotateId id pt :: acc) elems (moveTopDown pt) [])
    | DecInfix _ => []
    | DecInfixr _ => []
    | DecNonfix _ => []
    | DecStructure {elems = {args, ...}, ...} =>
      #1 (onList (fn ({id, constraint, bind, ...}, pt, acc) => let
        val pt = moveDown pt
        val (acc1, pt) = annotateConstraint constraint (moveRight pt) [annotateId id pt]
        val r = case bind of
          NONE => acc1
        | SOME {strexp, ...} => annotateStrexp strexp pt :: acc1
        in mkList r :: acc end) args (moveTopDown pt) [])
    | DecSignature {elems = {args, ...}, ...} =>
      #1 (onList (fn ({id, bind, ...}, pt, acc) => let
        val pt = moveDown pt
        val bind = case bind of
          NONE => []
        | SOME {sigexp, ...} => [annotateSigexp sigexp (moveRight pt)]
        in mkList (annotateId id pt :: bind) :: acc end) args (moveTopDown pt) [])
    | DecInclude {sigexps, ...} =>
      #1 (onList (fn (e, pt, acc) => annotateSigexp e pt :: acc) sigexps (moveTopDown pt) [])
    | Sharing {elems = {args, ...}, ...} =>
      #1 (onList (fn (id, pt, acc) => (* FIXME: PolyML bug (pt is missing) *)
        annotateId id pt :: acc) args (moveTopDown pt) [])
    | DecFunctor {elems = {args, ...}, ...} =>
      #1 (onList (fn ({id, funarg, constraint, bind, ...}, pt, acc) => let
        val pt = moveDown pt
        val id = annotateId id pt
        val pt = moveRight pt
        val (acc1, pt) = case funarg of
          ArgIdent {strid, ty} => (
          case annotateId strid NONE of strid =>
          case ty of
            NONE => ([strid, id], pt)
          | SOME {sigexp, ...} => ([annotateSigexp sigexp pt, strid, id], moveRight pt))
        | ArgSpec dec => case annotateDecs dec (PTInner pt) [id] of
          (acc, pt) => (acc, topAsInner pt)
        val (acc1, pt) = annotateConstraint constraint pt acc1
        val r = case bind of
          NONE => acc1
        | SOME {strexp, ...} => annotateStrexp strexp pt :: acc1
        in mkList r :: acc end) args (moveTopDown pt) [])
    | DecExp _           => raise Fail "unexpended top-level expression"
    | HOLTheory _        => raise Fail "unexpanded HOL syntax"
    | HOLDefinition _    => raise Fail "unexpanded HOL syntax"
    | HOLDatatype _      => raise Fail "unexpanded HOL syntax"
    | HOLQuoteDecl _     => raise Fail "unexpanded HOL syntax"
    | HOLInductiveDecl _ => raise Fail "unexpanded HOL syntax"
    | HOLType _          => raise Fail "unexpanded HOL syntax"
    | HOLSimpleThm _     => raise Fail "unexpanded HOL syntax"
    | HOLTheoremDecl _   => raise Fail "unexpanded HOL syntax"
    | DecExpansion _     => raise Fail "unreachable"
    in (withProps (decSpan d) (topHead pt) (rev children), moveTopRight pt) end

and annotateConstraint NONE pt acc = (acc, pt)
  | annotateConstraint (SOME {sigexp, ...}) pt acc =
    (annotateSigexp sigexp pt :: acc, moveRight pt)

and annotateSigexp (SigIdent id) pt = annotateId id pt
  | annotateSigexp sigexp pt =
    withProps (sigexpSpan sigexp) pt (case sigexp of
      SigIdent _ => raise Fail "unreachable"
    | Spec {spec, ...} => rev (#1 (annotateDecs spec (PTInner (moveDown pt)) []))
    | WhereType {sigexp, elems = {args, ...}, ...} =>
      case moveDown pt of pt => (* FIXME: PolyML bug (pt is missing) *)
      rev (#1 (onList (fn ({tybind, ...}, pt, acc) =>
        annotateTybind tybind pt :: acc) args (moveRight pt) [annotateSigexp sigexp pt])))

and annotateStrexp (StrIdent id) pt = annotateId id pt
  | annotateStrexp strexp pt =
    withProps (strexpSpan strexp) pt (case strexp of
      StrIdent _ => raise Fail "unreachable"
    | StrStruct {strdec, ...} => rev (#1 (annotateDecs strdec (PTInner (moveDown pt)) []))
    | StrConstraint {strexp, kind = {sigexp, ...}, ...} =>
      (case moveDown pt of pt => [annotateStrexp strexp pt, annotateSigexp sigexp (moveRight pt)])
    | FunAppExp {funid, strexp, ...} => (case moveDown pt of pt =>
      [annotateId funid pt, annotateStrexp strexp (moveRight pt)])
    | FunAppDec {funid, strdec, ...} => (case moveDown pt of pt =>
      annotateId funid pt :: rev (#1 (
        annotateDecs strdec (PTInner (moveDown (moveRight pt))) [])))
    | StrLetInEnd {strdec, strexp, ...} => let
      val (acc, pt) = annotateDecs strdec (PTInner (moveDown pt)) []
      in rev (annotateStrexp strexp (topAsInner pt) :: acc) end)

end

fun initialize old {
  text, filename, parseError, compilerOut, toplevelOut, progress, error,
  runtimeExn, mlParseTreeOld, mlParseTree, holParseTreeOld, holParseTree
} = if old then let
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
  val {feed, regular, finish, doDecl, ...} =
    HolParserOld.ToSML.mkPushTranslatorCore {
      filename = filename, parseError = parseError, quietOpen = true,
      read = fn _ => !sr before sr := ""
    } {
      regular = push o RegularChunk,
      aux = fn s => push (FlatChunk (NONE, Substring.full s)),
      strstr = encode HolParserOld.ToSML.strstr,
      strcode = encode HolParserOld.ToSML.strcode
    }
  val atEnd = ref false
  val pos = ref 0
  fun readChunk () =
    case !queue of
      s :: rest => (queue := rest; s)
    | [] => if !atEnd then EOFChunk else (
      case feed () of
        HolParserOld.Simple.TopDecl d => (holParseTreeOld d; pos := doDecl true (!pos) d)
      | HolParserOld.Simple.EOF p =>
        (regular (!pos, p); finish (); pos := p; atEnd := true);
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
      Reading ((base, reg), lo, _, _) => if reg then base + lo else base
    | EOF pos => pos
  val serial = ref 1
  fun ptFn NONE = ()
    | ptFn (SOME pt) = mlParseTreeOld pt
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
  in loop () end
else let
  datatype chunk
    = Chunk of string
    | PushSpan of (int * int) * bool ref
    | PopSpan of bool ref

  val sr = ref text
  val dummy = ref false
  val queue = DArray.new (100, PopSpan dummy)
  fun push chunk = DArray.push (queue, chunk)
  fun read _ = !sr before sr := ""
  val {parseDec, body, events, ...} =
    HOLParser.parseSML filename read parseError HOLParser.initialScope
  val fileline = HOLAst.mkFileline body events
  val expandDec = HOLToSML.expandDec
    {parseError = parseError, quietOpen = true, fileline = fileline}
  val lastPush = ref dummy
  val pr' = HOLPrinter.mkPrinter {
    str = push o Chunk,
    startSpan = fn i => (!lastPush := true; lastPush := ref false; push (PushSpan (i, !lastPush))),
    stopSpan = fn _ => (lastPush := ref false; push (PopSpan (!lastPush))) }
  val decsRef = ref []
  val ptRef = ref []
  fun fetchDec () =
    case parseDec () of
      NONE => true
    | SOME dec => (
      holParseTree dec;
      case expandDec dec of
        HOLAst.DecExpansion {result = [], ...} => fetchDec ()
      | dec => (
        decsRef := [dec];
        HOLPrinter.printDec parseError dec pr';
        false))
  val idx = ref 0
  val spans = ref []
  val pos = ref 0
  val tokidx = ref 0
  fun readChunk () = let
    val s = DArray.sub (queue, !idx)
    in idx := !idx+1; SOME s end
    handle Subscript => NONE
  fun toState () = case readChunk () of
      NONE => (tokidx := !tokidx + 2; (0, ""))
    | SOME (Chunk s) => (tokidx := !tokidx + 2; (0, PolyML.print s))
    | SOME (PushSpan (s, r)) => (
      spans := s :: !spans; lastPush := r; pos := #1 s; toState ())
    | SOME (PopSpan r) => (
      lastPush := r;
      case !spans of [] => () | s :: ss => (spans := ss; pos := #2 s);
      toState ())
  val curToken = ref (0, "")
  fun read2 () =
    case !curToken of
      (_, "") => NONE
    | (0, " ") => (curToken := toState (); SOME #" ")
    | (i, s) =>
      if i < size s then
        (curToken := (i+1, s); SOME (String.sub (s, i)))
      else (curToken := toState (); read2 ())
  val serial = ref 1
  fun ptFn pt = ptRef := moveDown pt :: !ptRef
  (* let
    open HOLAst
    fun split [] = NONE
      | split ((d as DecExpansion {orig, result}) :: decs) =
        (case split result of
          NONE => Option.map (fn (ds1, ds2) => (d :: ds1, ds2)) (split decs)
        | SOME (ds1, ds2) =>
          SOME ([DecExpansion {orig = orig, result = ds1}],
                 DecExpansion {orig = orig, result = ds2} :: decs))
      | split ((d as DecSemi _) :: decs) = SOME ([d], decs)
      | split (d :: decs) = Option.map (fn (ds1, ds2) => (d :: ds1, ds2)) (split decs)
    in
      case split (!decsRef) of
        NONE => ()
      | SOME (ds1, ds2) =>
        (PolyML.print ("go", ds1, ds2, buildList pt);
         app mlParseTree (#1 (annotateDecs ds1 (moveDown pt) [])); decsRef := ds2)
    end *)
  fun codeFn NONE () = ()
    | codeFn (SOME code) () = let
      val {fixes, values, structures, signatures, functors, types} = code ()
      fun enter f = app (f PolyML.globalNameSpace)
      in enter #enterFix fixes; enter #enterType types; enter #enterSig signatures;
        enter #enterStruct structures; enter #enterFunct functors; enter #enterVal values end
  fun getOffset () =
    if #1 (!curToken) = 0 then !pos else
    case (!lastPush, !spans) of
      (ref false, s :: _) => #2 s
    | _ => !pos
  (* This is a hack to cause PolyML to not collapse nodes with the same offset.
     We will not use line numbers from PolyML. *)
  fun getTokIdx () = if #1 (!curToken) = 0 then !tokidx else !tokidx + 1
  open PolyML.Compiler
  val parameters = (if !compile then [] else noCompile) @ [
    CPOutStream compilerOut,
    CPPrintStream toplevelOut,
    CPErrorMessageProc error,
    CPCompilerResultFun (fn (pt, code) => (ptFn pt; codeFn code)),
    CPLineNo getTokIdx,
    CPLineOffset getOffset,
    CPPrintInAlphabeticalOrder false,
    CPBindingSeq (fn () => (fn n => n before serial := n + 1) (!serial))];
  fun finish () = (
    progress (!pos);
    case !curToken of
      (_, "") => ()
    | _ => ((PolyML.compiler (read2, parameters) () handle e => runtimeExn e); finish ()))
  fun loop () = (
    DArray.clear queue;
    if fetchDec () then () else (
      idx := 0; spans := []; ptRef := []; curToken := toState ();
      finish ();
      PolyML.print ("go", (!decsRef), map (Option.map build) (rev (!ptRef)));
      app mlParseTree (rev (#1 (annotateDecs (!decsRef) (PTTop (rev (!ptRef))) [])));
      loop ()))
  in loop () end;

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

fun getTrees text = let
  val out = ref []
  val _ = PolyML.print_depth 100
  val _ = HOL_IDE.initialize false {
    filename = "foo",
    text = text,
    parseError = fn _ => fn _ => (),
    compilerOut = fn _ => (),
    toplevelOut = fn _ => (),
    progress = fn _ => (),
    error = fn _ => (),
    runtimeExn = fn _ => (),
    mlParseTreeOld = fn _ => (),
    mlParseTree = fn t => out := t :: !out,
    holParseTreeOld = fn _ => (),
    holParseTree = fn _ => ()
  }
  in (!out) end
(*
  getTrees "Theory foo\nLibs list[alias = fo]";
*)
fun go () = let
  open HOLAst
  val dec = DecExp (Record
    {elems =
      {args =
      [LabEq {eq = 3, exp = IntegerConstant (5, "1"), lab = (1, "a")},
        LabEq {eq = 10, exp = IntegerConstant (12, "2"), lab = (8, "b")}],
      delims = [SOME 6], stop = 13}, left = 0, right = SOME 13, stop = 14})
  val expandDec = HOLToSML.expandDec
    {parseError = fn _ => fn _ => (), quietOpen = true,
      fileline = fn _ => {file="",line=0,col=0}}
  in expandDec dec end
