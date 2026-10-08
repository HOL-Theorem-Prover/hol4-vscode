# HOL4 mode for Visual Studio Code

Support for working with the [HOL4 interactive theorem
prover](https://hol-theorem-prover.org) in Visual Studio Code. This
plugin provides the required functionality to maintain a HOL session
in an editor window, basic syntax highlighting, and Unicode input.
Everything else — diagnostics, hover,
go-to-definition, the outline, symbol search and completion — comes
from the HOL language server; see below.

## Requirements

Expects a HOL4 installation to exist, and the environment variable
`$HOLDIR` to point to this installation. The HOL4 homepage can be
found [here](https://hol-theorem-prover.org) and its GitHub repository
[here](https://github.com/HOL-Theorem-Prover/HOL). The HOL4 version
must be very recent (October 2026 or later): `bin/hol lsp` must be a
valid subcommand, and evaluating a selection needs a language server
that evaluates at a position and reports what a chunk bound. See
[`tools-poly/lsp/README.md`](https://github.com/HOL-Theorem-Prover/HOL/blob/develop/tools-poly/lsp/README.md)
in the HOL4 repository for the server contract.



## HOL4 LSP integration

When `hol4-mode.lsp.enabled` is `true` (the default), the extension
starts a HOL4 [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
client that speaks to `bin/hol lsp`.  This delivers:

- **Compile-driven diagnostics** in the Problems panel and inline
  squiggles as you edit.
- **Hover** with type information from the running HOL session, a
  theorem's statement when the cursor is on one, and the identifier's
  Reference entry where it has one, with a link to the entry's file.
  The entries come from `Manual/build/Docfiles-processed`, which a
  normal `bin/build` writes; a HOL built with `--no-helpdocs` has
  none, and hovers there carry the type alone.
- **Outline, symbol search and completion** — `Ctrl+Shift+O` for a
  file's declarations, `Ctrl+T` to search stored theorems, and
  completion of names in scope.  Symbol search covers the theories
  this script loads and, beyond them, any theory built in the project:
  those are marked *not an ancestor*, since using one means adding it
  to `Ancestors` first.
  **Theorem search** — `Ctrl+H Ctrl+Shift+M`, or *HOL: Search for
  theorems* in the command palette, asks the theorem database what
  matches. It prompts for one selector at a time and searches when you
  submit an empty one, `Escape` abandoning the search instead. A
  selector is a theory in single quotes, a fragment of a theorem's
  name in double quotes, or a term pattern, and several of them narrow
  rather than widen — so `x + 0n = x` and then `'arithmetic'` asks for
  that theory's theorems matching the pattern. The hits arrive as a
  quick pick that filters as you type; picking one opens the script
  where it was proved. This is emacs's `M-h M-M`, and searches
  statements, where `Ctrl+T` searches names.
- **HOL Goals side pane** — press `Ctrl+H Ctrl+G` to open a pane that
  follows the cursor and shows the proof state at each tactic step
  inside a `Proof … QED` block.
- **Evaluate selection** — `Ctrl+H Ctrl+E`, or *HOL: Evaluate
  selection* in the command palette, runs the selected text in the
  server's own HOL session and appends what it printed to the *HOL4
  LSP Eval* output channel.

  With nothing selected it asks for an expression instead (also *HOL:
  Evaluate expression…*), offering the ones already asked for this
  session, newest first. That is emacs's `M-h s`, and it is there so
  that evaluating something the script does not contain does not mean
  typing it into the script and deleting it again.

  It is evaluated **where the cursor is**. A file's declarations run
  in order, so what is in scope is what the compile had reached by
  there: a name bound further down the file is not available. This is
  the supported form of a trick that otherwise works by accident —
  typing `val x = <expr>` into blank space and hovering `x` — and it
  reads the same state without editing the buffer. What one
  evaluation binds, the next one at the same place can use.

  A compile may be holding the session, in which case the server says
  so and the command can simply be repeated. Evaluating a selection is
  emacs's `M-h M-E`.

### The `Ctrl+H` prefix, on every platform including macOS

Every HOL command chord starts with `Ctrl+H`, macOS included.  `Cmd+H`
would be the platform-native choice, but it is the key equivalent of
*Hide* on the application menu

### Positions and the pane width

The server picks its LSP position encoding from what this client
advertises, which is `utf-16` — so hover, go-to-definition and the
squiggles in the Problems panel land on the right characters even on
lines carrying `∀`, `⇒` or `‘…’`.

The Goals pane measures its own width and tells the server, so HOL's
pretty printer breaks lines to fit the pane you actually have rather
than a fixed 75 columns.  Resizing the pane re-renders at the new
width.

### A script whose ancestors will not load is left alone

The server refuses to compile a script that names a theory or library
it cannot load — one that has not been built yet, or that raises on
load.  With an ancestor missing there is nothing to elaborate the file
against, so every name the file takes from that ancestor would draw
its own error; instead you get one diagnostic, on the `Ancestors` /
`Libs` entry that named the missing module, and nothing else in the
file is compiled.  The status bar reads `HOL LSP: not compiling` and
the Goals pane says why.

Build the missing dependency with `Holmake`, then edit the file's
`Ancestors` / `Libs` header — any change to that list, including a
change and its undo — and the server tries again. If the header is
already right, `HOL: Compile the active script again` retries without
touching the file.

### One server per script

A `bin/hol lsp` process can serve exactly one theory script for its
lifetime.  Loading a script's ancestors puts them in the theory graph
and *seals* them, and the seal is a process-global soundness gate
against cross-theory redefinition: a second script's ancestors can
then be neither re-read nor withdrawn.  A shared server does not fail
loudly, it answers with wrong goal states and dead hovers.

So the extension starts one server per `*Script.sml` file, when that
file first becomes visible, and stops it when the file is closed.
Each server runs in its script's own directory, so it picks up the
`Holmakefile` (and any `HOLHEAP`) that governs that script.

Two consequences worth knowing:

- Each server loads a HOL heap, which costs a few seconds and a few
  hundred megabytes.  Opening ten scripts at once starts ten of them.
- `.sig` files and non-script `.sml` files get no server.  They
  declare no theory of their own, so there is no goal state to show.

Related settings:

- `hol4-mode.lsp.enabled` (default: `true`) — toggle the client
  entirely.  With `false` the extension behaves as it did before
  the LSP integration.
- `hol4-mode.lsp.executable` (default: empty) — override the path
  to `bin/hol`.  Falls back to `hol4-mode.holdir/bin/hol`, then
  `$HOLDIR/bin/hol`.

Palette commands: `HOL: Toggle HOL Goals pane`, `HOL: Restart LSP
server for the active script`, `HOL: Show LSP output channel for the
active script`, `HOL: Compile the active script again`.  All but the
first, and the status bar item, act on the server belonging to the
script in the active editor.

### Recording the protocol traffic

A server that misbehaves only under VS Code is a question about what
the *client* asked for and in what order, which no server-side log can
answer.  Set

```json
"hol4-lsp.trace.server": "verbose"
```

and every request, notification and reply is written to a
`HOL4 LSP Trace: <file>` output channel, one per server, beside the
`HOL4 LSP: <file>` channel carrying that server's own output.
`messages` names each message without its parameters, which is enough
to establish ordering and much shorter.  The setting takes effect
without a restart, and it is a lot of output, so leave it off
otherwise.

The section is `hol4-lsp`, not `hol4-mode`: vscode-languageclient
resolves it from the client's id, and that id is shared by every
server so one setting covers them all.

## Typing HOL

HOL is written in Unicode — `∀x. P x ∧ Q x ⇒ R x` — and none of those
characters are on a keyboard. There are two ways to get them, and they
work at the same time.

**Type the ASCII you would have written anyway.** Inside a HOL term,
the ordinary ASCII operators are rewritten as you type:

| type | get | type | get | type | get |
|---|---|---|---|---|---|
| `/\` | ∧ | `==>` | ⇒ | `!` | ∀ |
| `\/` | ∨ | `<=>` | ⇔ | `?` | ∃ |
| `<=` | ≤ | `<>` | ≠ | `?!` | ∃! |

These are the eleven rules of the Emacs `hol-input` method, so the two
editors behave alike. `!!` gives you a literal `!` and `??` a literal
`?`; for anything else, undo immediately after a rewrite gives back
what you typed.

Because `!` is dereference in SML and `<=` is comparison, the rewriting
fires **only where HOL term syntax actually lives**: inside `‘…’`,
`“…”` and `` `…` `` quotations, and in the bodies of `Theorem`,
`Definition`, `Datatype` and `Inductive` blocks. A `Proof` body, a
`Termination` clause and the surrounding SML are left alone, as are
string literals and `Quote` blocks — the latter delimit an embedded
language such as CakeML, where HOL's notation does not belong.

Add your own rules with `hol4-mode.input.rules`:

```json
"hol4-mode.input.rules": { "IN": "∈", "SUBSET": "⊆" }
```

**Or use the backslash for everything else.** `\alpha` gives α,
`\r` gives ⇒, `\sub` gives ⊆; there are over 1600 of them. The
abbreviation is underlined while you type it and resolves as soon as it
can only mean one thing, or on <kbd>Tab</kbd>. Hover over any Unicode
character in a HOL script to be told how to type it.

**The backtick key writes HOL's quotation delimiters.** Press `` ` ``
and you get `‘’` with the cursor between them; press it again on the
empty pair and it becomes `“”`. On a closing delimiter it steps over
it, on an opening one it retypes the whole quotation as the other kind,
and with text selected it wraps the selection. This mirrors Emacs'
`holscript-dbl-backquote`. Set `hol4-mode.input.smartQuotes` to `false`
if you would rather type literal backticks.

## Extension Settings

There is no longer a `hol4-mode.indexing` setting.  The symbol
indexer it governed has been removed: the language server answers the
same requests from HOL itself rather than from a regex scan of the
sources, so there is one implementation and it is the one that knows
what the names mean.  Any `.hol-vscode` directory left in a workspace
(or in `$HOLDIR`) is now unused and can be deleted.

Suggested additions to `settings.json` for use with [VSCodeVim](https://github.com/VSCodeVim/Vim),
somewhat corresponding to the HOL4 Vim mode defaults:
```json
        {
            "before": [ "<leader>", "s" ],
            "commands": [ "hol4-mode.sendSelection" ]
        },
    ],
    "vim.normalModeKeyBindings": [
        {
            "before": [ "<leader>", "h" ],
            "commands": [ "hol4-mode.startSession" ]
        },
        {
            "before": [ "<leader>", "<leader>", "x" ],
            "commands": [ "hol4-mode.stopSession" ]
        },
        {
            "before": [ "<leader>", "s" ],
            "commands": [ "hol4-mode.sendSelection" ]
        },
        {
            "before": [ "<leader>", "<leader>", "s" ],
            "commands": [ "hol4-mode.sendUntilCursor" ]
        },
        {
            "before": [ "<leader>", "y" ],
            "commands": [ "hol4-mode.toggleShowTypes" ]
        },
        {
            "before": [ "<leader>", "a" ],
            "commands": [ "hol4-mode.toggleShowAssums" ]
        },
        {
            "before": [ "<leader>", "c" ],
            "commands": [ "hol4-mode.interrupt" ]
        }
    ]
}
```

## Known Issues

- Syntax highlighting is lacking. Logical terms are especially bad.
- Location pragmas are not inserted at calls to `{Co}Inductive`, `Datatype`,
  `Theorem`, nor in term quotations.
- Symbol search reaches only theories that have been built; a script
  never compiled by `Holmake` contributes only the declarations of the
  buffers you have open.
- `.sig` files and library `.sml` files get no IDE features: the
  server binds to one theory script per process.
