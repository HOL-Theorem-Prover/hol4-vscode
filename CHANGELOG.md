# Change Log

## 0.4.2

- A Holmake run no longer disappears the moment it finishes. *HOL: Run
Holmake in the directory of the current document* opened a terminal
whose shell was Holmake itself, and a terminal closes when its shell
exits — so the panel, and everything Holmake had printed into it, went
as soon as the build ended. A failed build, a clean one, and a Holmake
that was never installed all looked alike. The run is now a VS Code
task: its terminal stays, with the output still in it, and a non-zero
exit is reported as well. A run stopped by hand is not called a
failure, and a second run in a directory already building is refused
rather than raced.

- `Holmake` is looked for at `hol4-mode.holmake.executable`, then at
`bin/Holmake` under `hol4-mode.holdir`, then under `$HOLDIR`, and
finally on the `PATH`. Where none of those has it the command says so,
instead of opening a terminal that closes again at once — which is
what a Holmake that was not installed used to look like. The new
`hol4-mode.holmake.args` is passed to every run, so `["-j4"]` there
builds in parallel.

## 0.4.1

- An evaluation's result is laid out again. `3 * 13` answered with
`val`, a space, `it`, a space, `=` and so on down the left margin, one
to a line. The language server renders a value with Poly's pretty
printer, which hands over a line a piece at a time, and the streamed
form of the request passed each of those on as its own report for this
channel to write as a line. The server now keeps a line together until
it is whole. Needs a HOL whose language server streams whole lines;
against an older one the output is as it was.

- `Ctrl+H Ctrl+E` with nothing selected now asks for an expression
instead of sending the block of the script around the cursor, so
getting a value out of the session no longer means typing it into the
file and deleting it again — which is what the command was there to
avoid. The box offers what has already been asked for this session,
newest first, and the expression is evaluated at the cursor, so what is
in scope is what a selection there would have seen. Also on the palette
as *HOL: Evaluate expression…*. A selection, when there is one, is
evaluated as before.

## 0.4.0

- Selected text can be evaluated in the language server's own HOL
session with `Ctrl+H Ctrl+E`, or *HOL: Evaluate selection*, and
whatever it prints is appended to a *HOL4 LSP Eval* output channel.
With nothing selected, the block around the cursor is sent. Getting a
value out of the session used to mean typing `val x = ...` onto a
blank line and hovering the name, that being the only thing that read
the server's state; the chunk now carries the cursor's position
instead, so it is evaluated exactly where it sits and the file is
never touched. What one evaluation binds, the next one in the same
place can use. A compile may be holding the session, in which case the
server says so and the command can be repeated. Needs a HOL whose
language server evaluates at a position and reports what a chunk
bound; against an older one the command has nothing to show.

## 0.3.3

- A theorem you delete no longer lingers in the proof tally. Writing a
syntactically complete but failing `Theorem ... QED` correctly reported
one proof to look at; deleting the whole block left it reported for the
rest of the session, with the count wrong, the name still in the
tooltip, and the jump-to-outstanding-proof command landing on whatever
now occupied that line. The language server says which proofs a buffer
still declares, and the tally keeps only those. Needs a HOL whose
language server sends that list; against an older one the tally behaves
as it did.

## 0.3.2

- Enter no longer accepts whatever the completion widget is offering.
Typing `Proof` at the start of a line and pressing Enter inserted
`ProofStepPlan`, a structure that shares the prefix and was the only
thing on offer, because HOL's block keywords are not SML names and
the language server had nothing else to suggest. Enter now always
ends the line in a HOL script; Tab and Ctrl+Space still accept a
suggestion, and setting `editor.acceptSuggestionOnEnter` yourself
overrides this.

## 0.3.1

- A proof split up with `suspend` and finished off in `Resume` blocks
no longer counts as something to look at. The status bar reported
`proofs 2/3 (1 to look at)` for a file that was complete, because the
tally treated every status it did not recognise as a bad verdict.
Such a proof is now counted as checked, and is no longer listed among
the outstanding proofs the status bar jumps between.

## 0.3.0

- HOL's ASCII operators are now rewritten to Unicode as you type them,
with no leader key: `/\` gives ∧, `==>` gives ⇒, `!` gives ∀. These
replacements fire only inside HOL terms, so SML's `!` and `<=` are
left alone, and `!!` and `??` give back the literal characters.
- The backtick key now inserts HOL's Unicode quotation delimiters: one
press gives `‘’`, a second turns the empty pair into `“”`, and on an
existing quotation it steps over or retypes the delimiters.
- `‘…’` and `“…”` are declared as brackets, so bracket matching and
navigation now know about them.
- `hol4-mode.input.leader` and `hol4-mode.eagerReplacement` are
declared in the manifest at last; both were read but invisible in the
settings UI, and changing a setting no longer needs a window reload.
- The script header is highlighted: `Theory`, `Ancestors` and `Libs`
now colour as keywords, along with the theory name and any attributes.
`Quote`, `Resume` and `Finalise` blocks are recognised too.
- Fixed keywords losing their colour for the rest of a file. A HOL
binder's variable list was matched as "anything up to a dot", so a `!`
inside a tactic quotation such as ``Q.PAT_X_ASSUM `$! m` (MP_TAC o
Q.SPECL [...])`` ran past the closing backtick to the dot in `Q.SPECL`.
The quotation never closed, and every `Theorem`, `Proof`, `QED` and
`End` below it was coloured as quoted text. Across HOL's own sources
this affected 1,625 keywords in 22 files.
- `Datatype :` with a space before the colon is recognised, as the HOL
lexer allows.
- Every keyword that opens or closes a block — `Theory`, `Ancestors`,
`Libs`, `Theorem`, `Definition`, `Datatype`, `Inductive`, `Quote`,
`Resume`, `Finalise`, `Proof`, `QED`, `Termination`, `End` — now
carries the one scope `keyword.other.block.hol`. Previously each had
its own (`End` alone had three, depending on which block it closed),
so a theme with any rule more specific than `keyword` could render
them in different shades.
- `End` is no longer drawn in a different shade of red from the other
keywords. Bracket matching ignores case, and SML's `let`, `local`,
`struct` and `sig` all close with `end`, so HOL's `End` was taken for
one of them; with no opener in scope it was painted as an *unexpected*
bracket — a red carrying an alpha channel, drawn over the keyword
colour, which the token inspector does not report. Those four word
pairs have been dropped from `brackets`, which costs `let`/`end`
matching (in SML; in HOL, there is no `end` used for
`let`-expressions) and the auto-indent that went with it.

## 0.2.1

- Tool-tips over SML entry-points now include links to documentation,
where it is available.
- README updates.

## 0.1.0

First release under the new publisher (“HOL Developers”). Previously
published as `oskarabrahamsson.hol4-mode`; that extension is
deprecated in favour of this one. Dramatic shift of focus to use LSP;
previous interaction model is mostly not working.

## 0.0.20 and earlier

See the git history of the original repository.
