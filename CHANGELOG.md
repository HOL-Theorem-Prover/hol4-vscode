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
