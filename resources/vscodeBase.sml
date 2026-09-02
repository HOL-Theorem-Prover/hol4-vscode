structure VSCodeBase =
struct

(* `HOLSource' is HOL's current translator; `HolParserOld' was the
   previous one and is gone.  Same reader interface, one field more. *)
fun holdep text = let
  val {read, ...} =
      HOLSource.stringToReader {quietOpen = false, print = fn _ => ()} text
  in
    Binarymap.foldr (fn (a, _, r) => a :: r) [] (Holdep_tokens.reader_deps ("", read))
    handle e => []
  end

fun load_holdep text = app (fn s => qload s handle _ => ()) (holdep text)

end;
