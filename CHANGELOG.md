# Change Log

## Unreleased

- HOL's ASCII operators are now rewritten to Unicode as you type them,
with no leader key: `/\` gives ∧, `==>` gives ⇒, `!` gives ∀. These
are the eleven rules of the Emacs `hol-input` method. They fire only
inside HOL terms, so SML's `!` and `<=` are left alone, and `!!` and
`??` give back the literal characters.
- The backtick key now inserts HOL's Unicode quotation delimiters: one
press gives `‘’`, a second turns the empty pair into `“”`, and on an
existing quotation it steps over or retypes the delimiters. Ported from
Emacs' `holscript-dbl-backquote`.
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
- New `test/offline/grammar.js` checks the grammar against a small
TextMate stand-in; there was previously no test of the highlighting.

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
