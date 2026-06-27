# Blight syntax highlighting

A VS Code / Cursor extension that adds syntax highlighting for the Blight (`.bl`)
language via a TextMate grammar (`source.blight`).

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

## Build

From this directory:

```bash
npx @vscode/vsce package
```

This produces `blight-<version>.vsix`.

## Install

In Cursor, either use the Extensions view ("Install from VSIX...") or the CLI:

```bash
cursor --install-extension blight-0.1.1.vsix
```

Then reload the window and open any `.bl` file.
