# Blight for VS Code / Cursor

A VS Code / Cursor extension for the Blight (`.bl`) language: syntax highlighting via a
TextMate grammar (`source.blight`), plus a Language Server client for diagnostics, hover,
and go-to-definition (backed by `blight-lsp`, `crates/blight-lsp`).

## Syntax highlighting

It highlights:

- `;` line comments and `"..."` string literals (with `\" \\ \n \t` escapes)
- definers (`define`, `define-rec`, `define-by`, `deftotal`, `defdata`, `class`,
  `instance`, `signature`, `module`, `functor`, `trait`, `impl`, `effect`) and the
  name they bind
- special forms (`lam`, `match`, `the`, `let`, `region`, `pair`, `fst`, `snd`,
  `app`, `handle`, `plam`)
- tactic vocabulary (`refl`, `assumption`, `exact`, `intro`, `induction`, `cong`,
  `then`, `orelse`, `repeat`)
- type formers / built-ins (`Pi`, `Sigma`, `Path`, `PathP`, `Type`, `Rgn`,
  `String`, `Unit`, `IO`, `Handle`, `Ordering`, `Level`)
- the effect-row marker `!`, resource grades (`0` / `1` / `ω`), capitalized
  constructors, and brackets `() [] {}`

Colors come from your active editor theme.

## Language Server (diagnostics, hover, go-to-definition)

The extension starts `blight-lsp` (the executable built from `crates/blight-lsp` in this repo)
as a Language Server for every open `.bl` file. It reuses the exact same in-process elaboration
pipeline as `blight build`/the REPL, so what the editor reports never drifts from what the CLI
accepts.

**What works today:**

- **Diagnostics**: every top-level form with an error is reported (not just the first) as soon
  as you open or edit a `.bl` file.
- **Hover**: shows the inferred type of a global name (a `define`, a constructor, an effect
  operation) under the cursor. Locally-bound variables (e.g. inside a `lam`) are not resolved —
  this mirrors the REPL's `:type` command, which also elaborates in an empty local scope.
- **Go to definition**: jumps to the defining top-level form for a global name, a `defdata`
  constructor, or an `effect` operation.

**Not yet implemented** (tracked in `docs/roadmap-post-m6.md`'s Wave 1 / A1 notes): inline
sub-expression squiggles (diagnostics are top-level-form granularity), completion, rename,
workspace-wide symbol search, and hover/go-to-def for local variables.

### Setup

1. Build the server once: `cargo build -p blight-lsp` from the repo root (or `--release` for a
   faster binary). This produces `target/debug/blight-lsp` (or `target/release/blight-lsp`).
2. Either put that binary on your `PATH`, or point the extension at it directly via the
   `blight.serverPath` setting (Settings -> search "blight").
3. Reload the window and open a `.bl` file — the "Blight Language Server" output channel shows
   startup/log messages if something goes wrong.

If the server fails to start (e.g. not built yet), the extension shows an error notification
with the exact command to run.

## Build the extension itself

From this directory:

```bash
npm install
npm run compile
npx @vscode/vsce package
```

This produces `blight-<version>.vsix`.

## Install

In Cursor, either use the Extensions view ("Install from VSIX...") or the CLI:

```bash
cursor --install-extension blight-0.2.0.vsix
```

Then reload the window and open any `.bl` file.
