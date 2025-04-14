structure VSCodeBase =
struct

fun holdep text = let
  val {read, ...} = HolParser.stringToReader {quietOpen = false} text
  in
    Binarymap.foldr (fn (a, _, r) => a :: r) [] (Holdep_tokens.reader_deps ("", read))
    handle e => []
  end

fun load_holdep text = app (fn s => qload s handle _ => ()) (holdep text)

end;
