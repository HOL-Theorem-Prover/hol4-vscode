# HOL4 mode for Visual Studio Code

Support for working with the [HOL4 interactive theorem prover](https://hol-theorem-prover.org) in
Visual Studio Code. This plugin provides the required functionality to maintain a HOL session in an
editor window, basic syntax highlighting, and basic unicode input completion.
The plugin can index source files in the users current directory and provides basic
go-to-definition functionality for theorems, function definitions, and inductive relations.

## Requirements

Expects a HOL4 installation to exist, and the environment variable `$HOLDIR` to point to this
installation. The HOL4 homepage can be found [here](https://hol-theorem-prover.org) and its GitHub
repository [here](https://github.com/HOL-Theorem-Prover/HOL).

## HOL4 LSP integration

When `hol4-mode.lsp.enabled` is `true` (the default), the extension
starts a HOL4 [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
client that speaks to `bin/hol lsp`.  This delivers:

- **Compile-driven diagnostics** in the Problems panel and inline
  squiggles as you edit.
- **LSP-provided hover** with type information from the running HOL
  session (in addition to the existing symbol-index hover, which
  keeps working).
- **HOL Goals side pane** — press `Ctrl+H Ctrl+G` (or `Cmd+H Cmd+G`
  on macOS) to open a pane that follows the cursor and shows the
  proof state at each tactic step inside a `Proof … QED` block.

Requirements: a HOL4 build recent enough that `bin/hol lsp` is a
valid subcommand.  See [`tools-poly/lsp/README.md`](https://github.com/HOL-Theorem-Prover/HOL/blob/develop/tools-poly/lsp/README.md)
in the HOL4 repository for the server contract.

Related settings:

- `hol4-mode.lsp.enabled` (default: `true`) — toggle the client
  entirely.  With `false` the extension behaves as it did before
  the LSP integration.
- `hol4-mode.lsp.executable` (default: empty) — override the path
  to `bin/hol`.  Falls back to `hol4-mode.holdir/bin/hol`, then
  `$HOLDIR/bin/hol`.

Palette commands: `HOL: Toggle HOL Goals pane`, `HOL: Restart LSP
server`, `HOL: Show LSP output channel`.

## Extension Settings

It is possible to toggle the indexing of theorems and definitions in the workspace from the settings
by the key: `hol4-mode.indexing` to `false`.

Suggested additions to `settings.json` for use with [VSCodeVim](https://github.com/VSCodeVim/Vim),
somewhat corresponding to the HOL4 Vim mode defaults:
```json
{
    "vim.visualModeKeyBindings": [
        {
            "before": [ "<leader>", "e" ],
            "commands": [ "hol4-mode.sendTactic" ]
        },
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
            "before": [ "<leader>", "g" ],
            "commands": [ "hol4-mode.sendGoal" ]
        },
        {
            "before": [ "<leader>", "S" ],
            "commands": [ "hol4-mode.sendSubgoal" ]
        },
        {
            "before": [ "<leader>", "e" ],
            "commands": [ "hol4-mode.sendTactic" ]
        },
        {
            "before": [ "<leader>", "p" ],
            "commands": [ "hol4-mode.proofmanShow" ]
        },
        {
            "before": [ "<leader>", "b" ],
            "commands": [ "hol4-mode.proofmanBack" ]
        },
        {
            "before": [ "<leader>", "R" ],
            "commands": [ "hol4-mode.proofmanRestart" ]
        },
        {
            "before": [ "<leader>", "r" ],
            "commands": [ "hol4-mode.proofmanRotate" ]
        },
        {
            "before": [ "<leader>", "d" ],
            "commands": [ "hol4-mode.proofmanDrop" ]
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

- Syntax highlighting is lacking. Logical terms are especially bad. The situation
  could be improved by implementing a HOL language server.
- There is some hacky code that attempts to strip ML comments from input that is
  being sent to HOL. Currently, this does not properly deal with nested comments,
  or comment tokens that exist within string literals.
- Comments are not stripped from tactic text.
- `load` calls are not inserted when calls to qualified ML code is made.
- Location pragmas are not inserted at calls to `{Co}Inductive`, `Datatype`,
  `Theorem`, nor in term quotations.
- Definitions created with `Define` are not properly indexed.
- Automatically generated theorems (for example, inductions) are not properly
  indexed.
- The hover/symbol-providers won't work on fully qualified identifiers (such as
  `myTheory.my_theorem`).
