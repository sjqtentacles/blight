//! `blight-lsp` — a minimal Language Server Protocol server for Blight. UNTRUSTED tooling; never
//! touches the kernel or re-checker trust boundary (it only calls the same untrusted
//! `blight-elab` pipeline the CLI/REPL use).
//!
//! Reuses the exact in-process elaboration pipeline (`blight_elab::program::Program`) rather than
//! shelling out to the `blight` binary, so editor-reported errors never drift from `blight build`.
//!
//! ## Scope (Wave 1 / A1b MVP, extended by Wave 9 / T1 "LSP v2")
//! - **Diagnostics**: every open/changed buffer is re-run from a fresh [`ElabEnv`] through
//!   [`Program::check_all_diagnostics`] (Wave 1 / A1a), so a buffer with several unrelated errors
//!   reports all of them at once, not just the first. T1 additionally narrows an unbound-name
//!   diagnostic down to the offending sub-expression via `blight_elab::scope::narrow_span`
//!   (already wired into `Program`), instead of the whole top-level form.
//! - **Hover**: shows the inferred type of the identifier under the cursor. Globals (a `define`d
//!   name, a constructor, an effect operation) resolve as before. T1 adds `let`-bound locals: the
//!   binding's right-hand side is re-elaborated standalone (`blight_elab::scope::resolve_let_rhs_at`)
//!   to recover its type. `lam`/pattern-bound locals remain unsupported (documented, not a bug —
//!   recovering their type needs more than a spanless re-elaboration of one subexpression).
//! - **Go to definition**: resolves a global name to the source span of its defining top-level
//!   form, via a lightweight form-head scan over [`read_all_spanned`] (no elaborator change):
//!   `define`, `define-rec`/`deftotal`, `defdata` (+ its constructors), `class`, `effect` (+ its
//!   operations), and `define-macro`. T1 extends the scan across `(load "path")` targets that
//!   resolve to an on-disk file (recursively, cycle-guarded), so jumping into a loaded file's
//!   definition opens *that* file rather than stopping at the `(load …)` form.
//! - **Rename**: local binders (`lam`/`let`/`Pi`/`Sigma`/`plam`/`match`/`matchx`/`handle`/
//!   `region`) only, via `blight_elab::scope::rename_local_binder`'s pure syntactic, scope-aware
//!   walk. A rename that would let a nested binder capture an occurrence is refused with an error
//!   response rather than silently producing a wrong rename. Renaming a *global* is not yet
//!   implemented (tracked, not silently dropped).
//!
//! ## Deliberately out of scope for this round (tracked, not silently dropped — see the roadmap's
//! ## "Gotcha ledger")
//! - Full span-threading through `Surface`/`ElabError`/kernel `TypeError` (a large refactor of the
//!   ~6k-line elaborator); the above features are delivered via a lexical re-scan of the
//!   pre-elaboration spanned s-expression tree instead (`blight_elab::scope`), which covers the
//!   common cases without touching the elaborator's trust-irrelevant-but-large internals.
//! - Hover/rename for `lam`/pattern-bound locals (only their *existence* is scope-tracked, not
//!   their type), completion, workspace symbols, renaming globals.
//! - Cross-file jump into the *embedded* prelude (no on-disk file to point an editor at) — only
//!   `(load …)` targets that actually resolve to a file on disk get a cross-file `Location`.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use blight_elab::diagnostic::Diagnostic as ElabDiagnostic;
use blight_elab::scope::{rename_local_binder, resolve_let_rhs_at, RenameError};
use blight_elab::sexpr::{read_all_spanned, Span, Spanned, SpannedSexpr};
use blight_elab::{ElabEnv, ElabError, Program};
use lsp_server::{Connection, ExtractError, Message, RequestId, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{Completion, Formatting, GotoDefinition, HoverRequest, Rename};
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionOptions, CompletionResponse,
    Diagnostic as LspDiagnostic, DiagnosticSeverity, GotoDefinitionResponse, Hover, HoverContents,
    HoverProviderCapability, InitializeParams, Location, MarkupContent, MarkupKind, OneOf,
    Position, PublishDiagnosticsParams, Range, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextEdit, Uri, WorkspaceEdit,
};

fn main() -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let (connection, io_threads) = Connection::stdio();

    let capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Left(true)),
        // E8: whole-document formatting via the shared `blight_elab::format_source`.
        document_formatting_provider: Some(OneOf::Left(true)),
        // E8: completion. `"` and `/` re-trigger inside `(load "std/…")` path strings; ordinary
        // identifier completion is client-initiated as the user types.
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec!["\"".into(), "/".into()]),
            ..Default::default()
        }),
        ..Default::default()
    };
    let init_params_value = connection.initialize(serde_json::to_value(capabilities)?)?;
    let _init_params: InitializeParams = serde_json::from_value(init_params_value)?;

    main_loop(&connection)?;
    io_threads.join()?;
    Ok(())
}

fn main_loop(connection: &Connection) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    // Keyed by the URI's string form rather than `Uri` itself: `Uri` derefs to `fluent_uri::Uri`,
    // whose `Hash`/`Eq` are manually forwarded through `as_str()` (see lsp-types' `uri.rs`) over a
    // representation that clippy can't statically prove is free of interior mutability
    // (`mutable_key_type`) — using the string it already hashes/compares by sidesteps the lint
    // without changing any lookup behavior (equal URIs still collide to the same entry).
    let mut docs: HashMap<String, DocState> = HashMap::new();
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                // `handle_shutdown` itself blocks waiting for (and consumes) the follow-up `exit`
                // notification before returning `true` — so by the time we get here, both halves
                // of the shutdown handshake are done. We exit the process directly rather than
                // returning and relying on `io_threads.join()`: that join waits for the
                // stdin-reader thread to observe EOF, which only happens once the client closes
                // its end of the pipe. Nothing guarantees *when* that happens, and the LSP spec's
                // intent for `exit` is immediate termination, not "eventually, once the pipe
                // closes".
                if connection.handle_shutdown(&req)? {
                    std::process::exit(0);
                }
                handle_request(connection, req, &docs)?;
            }
            Message::Notification(note) => {
                // A client that sends a bare `exit` without a preceding `shutdown` request (not
                // spec-compliant, but cheap to tolerate) still terminates promptly.
                if note.method == "exit" {
                    std::process::exit(0);
                }
                handle_notification(connection, note, &mut docs)?;
            }
            Message::Response(_) => {}
        }
    }
    Ok(())
}

// ---- per-document analysis ------------------------------------------------------------------

/// One buffer's cached analysis, rebuilt from scratch on every open/change. The pipeline is a
/// batch, not an incremental, one (`ElabEnv::new()` is cheap — see the roadmap's LSP gotcha
/// notes), so re-running the whole buffer on every keystroke is the correct MVP strategy, not a
/// shortcut.
struct DocState {
    text: String,
    diagnostics: Vec<ElabDiagnostic>,
    /// Every global/constructor/effect-op name's defining location, for go-to-def — including
    /// names defined in a `(load "path")` target that resolves to an on-disk file (Wave 9 / T1).
    definitions: HashMap<String, DefLocation>,
    /// The environment after processing the whole buffer (rolled back per-form on error by
    /// `check_all_diagnostics`, so this contains every successfully-elaborated declaration even
    /// past an earlier error) — used for hover type lookups.
    env: ElabEnv,
}

/// Where a name is defined: `file: None` means "this buffer, at `span`"; `file: Some(path)` means
/// an on-disk file reached transitively through `(load …)`, at `span` within *that* file's text.
#[derive(Debug, Clone)]
struct DefLocation {
    file: Option<PathBuf>,
    span: Span,
}

fn analyze(text: &str, base_dir: &Path) -> DocState {
    let mut env = ElabEnv::new();
    let diagnostics = {
        let mut prog = Program::with_resolver(&mut env, |path: &str| resolve(base_dir, path));
        prog.check_all_diagnostics(text)
    };
    let definitions = collect_definitions(text, base_dir);
    DocState {
        text: text.to_string(),
        diagnostics,
        definitions,
        env,
    }
}

/// Mirrors the CLI's `cli_load` (`blight-repl/src/main.rs`): try the file relative to `base_dir`,
/// then the bare path, then the sources embedded in this binary — so `(load "std/nat.bl")` works
/// with no source checkout, exactly like `blight build`.
fn resolve(base_dir: &Path, path: &str) -> Result<String, ElabError> {
    let candidates = [base_dir.join(path), Path::new(path).to_path_buf()];
    for cand in &candidates {
        if let Ok(src) = std::fs::read_to_string(cand) {
            return Ok(src);
        }
    }
    if let Some(src) = blight_prelude_embed::embedded(path) {
        return Ok(src.to_string());
    }
    Err(ElabError::BadForm(format!(
        "cannot load {path:?}: not found on disk and not a bundled prelude module"
    )))
}

/// A pragmatic go-to-definition index: scan every top-level form's head for a name-introducing
/// keyword and record `name -> that form's location`, without touching the elaborator (no
/// def-site span table exists there today). Also indexes `defdata`'s constructors and `effect`'s
/// operations, since those are exactly what a reader hovers/jumps from. Follows `(load "path")`
/// into any target that resolves to an on-disk file (recursively, cycle-guarded via `visited`),
/// so a name defined in a loaded file is indexed too — with `DefLocation::file` recording which
/// file it actually lives in (Wave 9 / T1's cross-file jump).
fn collect_definitions(text: &str, base_dir: &Path) -> HashMap<String, DefLocation> {
    let mut out = HashMap::new();
    let mut visited = HashSet::new();
    index_source(text, base_dir, None, &mut out, &mut visited);
    out
}

fn index_source(
    text: &str,
    base_dir: &Path,
    file: Option<&Path>,
    out: &mut HashMap<String, DefLocation>,
    visited: &mut HashSet<PathBuf>,
) {
    let Ok(forms) = read_all_spanned(text) else {
        return;
    };
    for form in &forms {
        index_form(form, file, out);
        let SpannedSexpr::List(items) = &form.node else {
            continue;
        };
        let is_load =
            matches!(items.first().map(|s| &s.node), Some(SpannedSexpr::Atom(kw)) if kw == "load");
        if !is_load {
            continue;
        }
        let Some(path_str) = atom_string_literal(items, 1) else {
            continue;
        };
        let Some(target) = resolve_path_on_disk(base_dir, &path_str) else {
            continue;
        };
        let target = target.canonicalize().unwrap_or(target);
        if !visited.insert(target.clone()) {
            continue;
        }
        if let Ok(sub_src) = std::fs::read_to_string(&target) {
            let sub_base = target
                .parent()
                .map(Path::to_path_buf)
                .unwrap_or_else(|| base_dir.to_path_buf());
            index_source(&sub_src, &sub_base, Some(&target), out, visited);
        }
    }
}

/// The decoded contents of a string-literal atom at `items[i]`, if there is one.
fn atom_string_literal(items: &[Spanned<SpannedSexpr>], i: usize) -> Option<String> {
    match items.get(i).map(|s| &s.node) {
        Some(SpannedSexpr::Atom(a)) if a.starts_with('"') && a.ends_with('"') && a.len() >= 2 => {
            Some(a[1..a.len() - 1].to_string())
        }
        _ => None,
    }
}

/// Mirrors `resolve`'s on-disk candidates (relative to `base_dir`, then bare), but — unlike
/// `resolve` — never falls back to the embedded prelude, since there is no file on disk to point
/// an editor's go-to-definition at for those.
fn resolve_path_on_disk(base_dir: &Path, path: &str) -> Option<PathBuf> {
    [base_dir.join(path), Path::new(path).to_path_buf()]
        .into_iter()
        .find(|c| c.is_file())
}

fn index_form(
    form: &Spanned<SpannedSexpr>,
    file: Option<&Path>,
    out: &mut HashMap<String, DefLocation>,
) {
    let SpannedSexpr::List(items) = &form.node else {
        return;
    };
    let Some(Spanned {
        node: SpannedSexpr::Atom(kw),
        ..
    }) = items.first()
    else {
        return;
    };
    let record = |name: String, out: &mut HashMap<String, DefLocation>| {
        out.entry(name).or_insert(DefLocation {
            file: file.map(Path::to_path_buf),
            span: form.span,
        });
    };
    match kw.as_str() {
        "define" | "define-rec" | "deftotal" | "define-macro" | "class" => {
            if let Some(name) = atom_at(items, 1) {
                record(name, out);
            }
        }
        // `(defdata D (params...) (Con (field ty)...)...)`: index `D` and every constructor head.
        "defdata" => {
            if let Some(name) = atom_at(items, 1) {
                record(name, out);
            }
            for item in items.iter().skip(2) {
                if let SpannedSexpr::List(sub) = &item.node {
                    if let Some(cname) = atom_at(sub, 0) {
                        record(cname, out);
                    }
                }
            }
        }
        // `(effect E (op ParamTy ResultTy)...)`: index `E` and every operation head.
        "effect" => {
            if let Some(name) = atom_at(items, 1) {
                record(name, out);
            }
            for item in items.iter().skip(2) {
                if let SpannedSexpr::List(sub) = &item.node {
                    if let Some(opname) = atom_at(sub, 0) {
                        record(opname, out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn atom_at(items: &[Spanned<SpannedSexpr>], i: usize) -> Option<String> {
    match items.get(i) {
        Some(Spanned {
            node: SpannedSexpr::Atom(a),
            ..
        }) => Some(a.clone()),
        _ => None,
    }
}

/// The identifier atom whose span contains `offset`, if any (innermost match wins, so a name deep
/// inside a nested form resolves to itself rather than the whole enclosing list).
fn word_at(text: &str, offset: usize) -> Option<String> {
    let forms = read_all_spanned(text).ok()?;
    forms.iter().find_map(|f| atom_at_offset(f, offset))
}

fn atom_at_offset(node: &Spanned<SpannedSexpr>, offset: usize) -> Option<String> {
    if offset < node.span.start || offset >= node.span.end {
        return None;
    }
    match &node.node {
        SpannedSexpr::Atom(a) if !a.starts_with('"') => Some(a.clone()),
        SpannedSexpr::Atom(_) => None,
        SpannedSexpr::List(items) => items.iter().find_map(|i| atom_at_offset(i, offset)),
    }
}

fn hover_at(doc: &DocState, offset: usize) -> Option<Hover> {
    let word = word_at(&doc.text, offset)?;
    // Elaborates `word` as a standalone expression against `doc.env`, exactly like the REPL's
    // `:type` command; works for globals and nullary constructors, not for local (`lam`-bound)
    // variables, since elaboration here uses an empty local scope (see the shared
    // `blight_elab::infer_type_str` doc-comment — this used to be an independent copy).
    if let Ok(ty) = blight_elab::infer_type_str(&doc.env, &word) {
        return Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::PlainText,
                value: format!("{word} : {ty}"),
            }),
            range: None,
        });
    }
    // Not a global: try a `let`-bound local (Wave 9 / T1) by re-elaborating its right-hand side
    // standalone against the buffer's current global environment.
    let forms = read_all_spanned(&doc.text).ok()?;
    let rhs_span = forms.iter().find_map(|f| resolve_let_rhs_at(f, offset))?;
    let rhs_src = &doc.text[rhs_span.start..rhs_span.end];
    let ty = blight_elab::infer_type_str(&doc.env, rhs_src).ok()?;
    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::PlainText,
            value: format!("{word} : {ty}"),
        }),
        range: None,
    })
}

fn goto_definition_at(doc: &DocState, offset: usize, uri: &Uri) -> Option<GotoDefinitionResponse> {
    let word = word_at(&doc.text, offset)?;
    let loc = doc.definitions.get(&word)?;
    match &loc.file {
        None => {
            let range = span_to_range(&doc.text, loc.span);
            Some(GotoDefinitionResponse::Scalar(Location::new(
                uri.clone(),
                range,
            )))
        }
        // Wave 9 / T1: the definition lives in a `(load "path")` target on disk — read that file
        // to compute the range in *its* coordinates, and point the response at its own URI.
        Some(path) => {
            let text = std::fs::read_to_string(path).ok()?;
            let range = span_to_range(&text, loc.span);
            let target_uri = path_to_uri(path)?;
            Some(GotoDefinitionResponse::Scalar(Location::new(
                target_uri, range,
            )))
        }
    }
}

/// Rename the local binder whose declaration contains `offset` (Wave 9 / T1). Returns `Ok(None)`
/// when `offset` isn't on a recognized local-binder declaration (nothing to do — e.g. it's a
/// global, not yet supported by rename), `Ok(Some(edit))` on success, and `Err(message)` when the
/// rename would let a nested binder capture an occurrence (refused rather than silently applied).
fn rename_at(
    doc: &DocState,
    offset: usize,
    new_name: &str,
    uri: &Uri,
) -> Result<Option<WorkspaceEdit>, String> {
    let forms = read_all_spanned(&doc.text).map_err(|e| e.msg)?;
    match rename_local_binder(&forms, offset, new_name) {
        Ok(spans) => {
            let edits: Vec<TextEdit> = spans
                .into_iter()
                .map(|s| TextEdit {
                    range: span_to_range(&doc.text, s),
                    new_text: new_name.to_string(),
                })
                .collect();
            // `Uri`'s `Hash`/`Eq` are manually forwarded through `as_str()` (see `docs`'s comment
            // in `main_loop`) over a representation clippy can't statically prove is free of
            // interior mutability; `lsp_types::WorkspaceEdit` mandates this key type, so there is
            // no alternative representation to sidestep the lint with here.
            #[allow(clippy::mutable_key_type)]
            let mut changes = HashMap::new();
            changes.insert(uri.clone(), edits);
            Ok(Some(WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }))
        }
        Err(RenameError::NotABinder) => Ok(None),
        Err(RenameError::WouldCapture) => Err(format!(
            "renaming to `{new_name}` would be captured by a nested binder of the same name"
        )),
    }
}

// ---- E8: formatting + completion ---------------------------------------------------------------

/// Full-document formatting via the shared `blight_elab::format_source` (the same canonicalizer
/// behind `blight fmt` and the fmt_corpus idempotence/semantics gate). Contract, pinned by
/// `lsp_formatting_returns_fmt_output`: `None` when the buffer is lexically malformed (the
/// formatter never guesses at text it cannot re-read), an empty vec when the buffer is already
/// canonical, and exactly one whole-document `TextEdit` otherwise (idempotence of the formatter
/// makes the single replace edit safe — re-formatting the result is a no-op).
fn formatting_edits(doc: &DocState) -> Option<Vec<TextEdit>> {
    let formatted = blight_elab::format_source(&doc.text).ok()?;
    if formatted == doc.text {
        return Some(Vec::new());
    }
    Some(vec![TextEdit {
        range: Range {
            start: Position::new(0, 0),
            end: offset_to_position(&doc.text, doc.text.len()),
        },
        new_text: formatted,
    }])
}

/// The surface keywords offered by completion: the top-level heads from
/// `blight_elab::program::Program`'s dispatch (the same set `blight_elab::docs::DOC_KEYWORDS`
/// mirrors, plus the non-documenting heads) and the expression heads the elaborator and the
/// VS Code grammar's special-form rule recognize. Curated here because no single crate exports
/// the union; completion quality degrades gracefully if a keyword is missing, so a curated list
/// is acceptable where go-to-definition's exhaustive indexing would not be.
const KEYWORDS: &[&str] = &[
    // top-level declaration heads
    "define",
    "define-rec",
    "define-by",
    "define-macro",
    "defn",
    "deftotal",
    "defdata",
    "class",
    "instance",
    "effect",
    "foreign",
    "load",
    "import",
    // expression heads
    "lam",
    "plam",
    "let",
    "match",
    "the",
    "do",
    "handle",
    "perform",
    "pair",
    "fst",
    "snd",
    "region",
    "Pi",
    "Sigma",
    "Type",
    "Path",
];

/// If `offset` sits inside the string argument of a `(load "…")` form, return the path prefix
/// typed so far. Detected lexically over `text[..offset]` (a quote-parity scan), NOT via the
/// s-expression reader: mid-keystroke the string is unterminated, the buffer unreadable, and the
/// definitions index empty — exactly when this completion is wanted.
fn load_string_prefix(text: &str, offset: usize) -> Option<&str> {
    let before = &text[..offset.min(text.len())];
    // Walk the prefix tracking whether we are inside a string literal (honoring `\"` escapes),
    // remembering the opening quote of the string the cursor is in.
    let mut in_string = false;
    let mut escaped = false;
    let mut open = 0usize;
    for (i, c) in before.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
        } else if c == '"' {
            in_string = true;
            open = i;
        }
    }
    if !in_string {
        return None;
    }
    // The string is a `(load …)` argument iff the text before its opening quote ends with the
    // `load` head in operator position.
    let head = before[..open].trim_end();
    let head = head.strip_suffix("load")?;
    if !head.trim_end().ends_with(['(', '[']) {
        return None;
    }
    Some(&before[open + 1..])
}

/// Completion candidates at `offset` (E8). Inside a `(load "` string: the embedded std module
/// paths matching the typed prefix, and nothing else (keywords are noise inside a path string).
/// Otherwise: every indexed global/constructor/effect-op from `doc.definitions` plus the surface
/// [`KEYWORDS`], deduplicated and sorted (the client filters against the word at the cursor).
fn completions_at(doc: &DocState, offset: usize) -> Vec<CompletionItem> {
    if let Some(prefix) = load_string_prefix(&doc.text, offset) {
        return blight_prelude_embed::module_names()
            .iter()
            .filter(|m| m.starts_with(prefix))
            .map(|m| CompletionItem {
                label: (*m).to_string(),
                kind: Some(CompletionItemKind::FILE),
                detail: Some("embedded std module".to_string()),
                ..Default::default()
            })
            .collect();
    }
    let mut items: Vec<CompletionItem> = doc
        .definitions
        .keys()
        .map(|name| CompletionItem {
            label: name.clone(),
            // The definitions index doesn't record what kind of name it holds (define vs
            // constructor vs effect op); VALUE is the honest generic kind.
            kind: Some(CompletionItemKind::VALUE),
            ..Default::default()
        })
        .collect();
    items.extend(KEYWORDS.iter().map(|kw| CompletionItem {
        label: (*kw).to_string(),
        kind: Some(CompletionItemKind::KEYWORD),
        ..Default::default()
    }));
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items.dedup_by(|a, b| a.label == b.label);
    items
}

// ---- LSP position <-> byte-offset conversion (UTF-16, per the LSP default encoding) -----------
//
// This is deliberately separate from `blight_elab::diagnostic`'s char-counting `line_col` (which
// backs the CLI's caret-underlined error rendering): the LSP wire protocol counts *UTF-16 code
// units* per character, a different unit than `line_col`'s Unicode scalar count, so the two must
// not be conflated even though both start from the same byte-offset `Span`.

fn offset_to_position(text: &str, offset: usize) -> Position {
    let offset = offset.min(text.len());
    let line_start = text[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line = text[..line_start].bytes().filter(|&b| b == b'\n').count() as u32;
    let character: u32 = text[line_start..offset]
        .chars()
        .map(|c| c.len_utf16() as u32)
        .sum();
    Position::new(line, character)
}

fn position_to_offset(text: &str, pos: Position) -> usize {
    let mut line_start = 0usize;
    for _ in 0..pos.line {
        match text[line_start..].find('\n') {
            Some(i) => line_start += i + 1,
            None => return text.len(),
        }
    }
    let line_end = text[line_start..]
        .find('\n')
        .map(|i| line_start + i)
        .unwrap_or(text.len());
    let mut utf16_count = 0u32;
    for (byte_idx, ch) in text[line_start..line_end].char_indices() {
        if utf16_count >= pos.character {
            return line_start + byte_idx;
        }
        utf16_count += ch.len_utf16() as u32;
    }
    line_end
}

fn span_to_range(text: &str, span: Span) -> Range {
    Range::new(
        offset_to_position(text, span.start),
        offset_to_position(text, span.end),
    )
}

// ---- URI <-> filesystem path (minimal `file://` handling; no query/fragment support needed) ---

fn uri_to_path(uri: &Uri) -> PathBuf {
    let s = uri.as_str();
    let path_part = s.strip_prefix("file://").unwrap_or(s);
    PathBuf::from(percent_decode(path_part))
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let Ok(byte) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                out.push(byte);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn base_dir_for_uri(uri: &Uri) -> PathBuf {
    let path = uri_to_path(uri);
    path.parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."))
}

/// The inverse of [`uri_to_path`]/[`percent_decode`]: build a `file://` URI for an absolute
/// filesystem path (used by cross-file go-to-definition, Wave 9 / T1, to point at a `(load …)`
/// target). Percent-encodes everything outside the RFC 3986 "unreserved" set plus `/`, which is
/// conservative (some legal path characters get encoded that needn't be) but always produces a
/// valid, round-trippable URI.
fn path_to_uri(path: &Path) -> Option<Uri> {
    let s = path.to_str()?;
    let mut encoded = String::with_capacity(s.len());
    for b in s.bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                encoded.push(b as char)
            }
            _ => encoded.push_str(&format!("%{b:02X}")),
        }
    }
    let uri_str = if encoded.starts_with('/') {
        format!("file://{encoded}")
    } else {
        format!("file:///{encoded}")
    };
    uri_str.parse().ok()
}

// ---- diagnostics publishing -------------------------------------------------------------------

fn publish_diagnostics(
    connection: &Connection,
    uri: &Uri,
    doc: &DocState,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let diagnostics: Vec<LspDiagnostic> = doc
        .diagnostics
        .iter()
        .map(|d| {
            let range = match d.span {
                Some(span) => span_to_range(&doc.text, span),
                None => Range::new(Position::new(0, 0), Position::new(0, 1)),
            };
            LspDiagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("blight".to_string()),
                message: d.message.clone(),
                ..Default::default()
            }
        })
        .collect();
    let params = PublishDiagnosticsParams {
        uri: uri.clone(),
        diagnostics,
        version: None,
    };
    connection
        .sender
        .send(Message::Notification(lsp_server::Notification::new(
            PublishDiagnostics::METHOD.to_string(),
            params,
        )))?;
    Ok(())
}

// ---- request/notification dispatch -------------------------------------------------------------

fn cast_request<R>(req: lsp_server::Request) -> Result<(RequestId, R::Params), lsp_server::Request>
where
    R: lsp_types::request::Request,
{
    match req.extract(R::METHOD) {
        Ok(pair) => Ok(pair),
        Err(ExtractError::MethodMismatch(req)) => Err(req),
        Err(ExtractError::JsonError { method, error }) => {
            // Malformed params for a method we do recognize: log and treat as unhandled rather
            // than crashing the server over one bad client message.
            eprintln!("blight-lsp: invalid params for {method}: {error}");
            Err(lsp_server::Request::new(
                RequestId::from(0),
                method,
                serde_json::Value::Null,
            ))
        }
    }
}

fn cast_notification<N>(
    note: lsp_server::Notification,
) -> Result<N::Params, lsp_server::Notification>
where
    N: lsp_types::notification::Notification,
{
    match note.extract(N::METHOD) {
        Ok(params) => Ok(params),
        Err(ExtractError::MethodMismatch(note)) => Err(note),
        Err(ExtractError::JsonError { method, error }) => {
            eprintln!("blight-lsp: invalid params for {method}: {error}");
            Err(lsp_server::Notification::new(
                method,
                serde_json::Value::Null,
            ))
        }
    }
}

fn handle_request(
    connection: &Connection,
    req: lsp_server::Request,
    docs: &HashMap<String, DocState>,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let req = match cast_request::<HoverRequest>(req) {
        Ok((id, params)) => {
            let uri = &params.text_document_position_params.text_document.uri;
            let result: Option<Hover> = docs.get(uri.as_str()).and_then(|doc| {
                let offset =
                    position_to_offset(&doc.text, params.text_document_position_params.position);
                hover_at(doc, offset)
            });
            connection
                .sender
                .send(Message::Response(Response::new_ok(id, result)))?;
            return Ok(());
        }
        Err(req) => req,
    };
    let req = match cast_request::<GotoDefinition>(req) {
        Ok((id, params)) => {
            let uri = params
                .text_document_position_params
                .text_document
                .uri
                .clone();
            let result: Option<GotoDefinitionResponse> = docs.get(uri.as_str()).and_then(|doc| {
                let offset =
                    position_to_offset(&doc.text, params.text_document_position_params.position);
                goto_definition_at(doc, offset, &uri)
            });
            connection
                .sender
                .send(Message::Response(Response::new_ok(id, result)))?;
            return Ok(());
        }
        Err(req) => req,
    };
    let req = match cast_request::<Rename>(req) {
        Ok((id, params)) => {
            let uri = params.text_document_position.text_document.uri.clone();
            let response = match docs.get(uri.as_str()) {
                Some(doc) => {
                    let offset =
                        position_to_offset(&doc.text, params.text_document_position.position);
                    match rename_at(doc, offset, &params.new_name, &uri) {
                        Ok(edit) => Message::Response(Response::new_ok(id, edit)),
                        Err(msg) => Message::Response(Response::new_err(
                            id,
                            lsp_server::ErrorCode::InvalidRequest as i32,
                            msg,
                        )),
                    }
                }
                None => Message::Response(Response::new_ok(id, None::<WorkspaceEdit>)),
            };
            connection.sender.send(response)?;
            return Ok(());
        }
        Err(req) => req,
    };
    // E8: whole-document formatting. `None` (unknown buffer or lexically malformed text) means
    // "no edits" — the client's format request quietly does nothing rather than erroring.
    let req = match cast_request::<Formatting>(req) {
        Ok((id, params)) => {
            let uri = &params.text_document.uri;
            let result: Option<Vec<TextEdit>> = docs.get(uri.as_str()).and_then(formatting_edits);
            connection
                .sender
                .send(Message::Response(Response::new_ok(id, result)))?;
            return Ok(());
        }
        Err(req) => req,
    };
    // E8: completion — globals/constructors/effect-ops + keywords, or std module paths inside a
    // `(load "` string.
    let req = match cast_request::<Completion>(req) {
        Ok((id, params)) => {
            let uri = &params.text_document_position.text_document.uri;
            let result: Option<CompletionResponse> = docs.get(uri.as_str()).map(|doc| {
                let offset = position_to_offset(&doc.text, params.text_document_position.position);
                CompletionResponse::Array(completions_at(doc, offset))
            });
            connection
                .sender
                .send(Message::Response(Response::new_ok(id, result)))?;
            return Ok(());
        }
        Err(req) => req,
    };
    connection.sender.send(Message::Response(Response::new_err(
        req.id,
        lsp_server::ErrorCode::MethodNotFound as i32,
        format!("blight-lsp: unhandled method {}", req.method),
    )))?;
    Ok(())
}

fn handle_notification(
    connection: &Connection,
    note: lsp_server::Notification,
    docs: &mut HashMap<String, DocState>,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let note = match cast_notification::<DidOpenTextDocument>(note) {
        Ok(params) => {
            let uri = params.text_document.uri.clone();
            let base_dir = base_dir_for_uri(&uri);
            let doc = analyze(&params.text_document.text, &base_dir);
            publish_diagnostics(connection, &uri, &doc)?;
            docs.insert(uri.as_str().to_string(), doc);
            return Ok(());
        }
        Err(note) => note,
    };
    let note = match cast_notification::<DidChangeTextDocument>(note) {
        Ok(params) => {
            let uri = params.text_document.uri.clone();
            // Full-document sync: the last (only) change event carries the entire new text.
            if let Some(change) = params.content_changes.into_iter().next_back() {
                let base_dir = base_dir_for_uri(&uri);
                let doc = analyze(&change.text, &base_dir);
                publish_diagnostics(connection, &uri, &doc)?;
                docs.insert(uri.as_str().to_string(), doc);
            }
            return Ok(());
        }
        Err(note) => note,
    };
    let note = match cast_notification::<DidCloseTextDocument>(note) {
        Ok(params) => {
            docs.remove(params.text_document.uri.as_str());
            return Ok(());
        }
        Err(note) => note,
    };
    let _ = note;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analyze_reports_all_errors_in_a_buffer() {
        let doc = analyze(
            "(defdata Nat () (Zero) (Succ (n Nat)))\n\
             (the Nat undefined-one)\n\
             (the Nat undefined-two)",
            Path::new("."),
        );
        assert_eq!(doc.diagnostics.len(), 2, "{:?}", doc.diagnostics);
    }

    #[test]
    fn definitions_index_finds_defdata_and_constructors() {
        let defs = collect_definitions("(defdata Nat () (Zero) (Succ (n Nat)))", Path::new("."));
        assert!(defs.contains_key("Nat"));
        assert!(defs.contains_key("Zero"));
        assert!(defs.contains_key("Succ"));
    }

    #[test]
    fn definitions_index_finds_define_and_effect_ops() {
        let defs = collect_definitions(
            "(define one (the Nat Zero))\n\
             (effect Clock (now Unit Nat))",
            Path::new("."),
        );
        assert!(defs.contains_key("one"));
        assert!(defs.contains_key("Clock"));
        assert!(defs.contains_key("now"));
    }

    #[test]
    fn word_at_finds_the_innermost_atom() {
        let src = "(define one (the Nat Zero))";
        let offset = src.find("Zero").unwrap();
        assert_eq!(word_at(src, offset), Some("Zero".to_string()));
    }

    #[test]
    fn hover_reports_the_type_of_a_global() {
        let doc = analyze("(defdata Nat () (Zero) (Succ (n Nat)))", Path::new("."));
        let offset = doc.text.rfind("Zero").unwrap();
        let hover = hover_at(&doc, offset).expect("Zero is a nullary constructor with a type");
        match hover.contents {
            HoverContents::Markup(m) => assert!(m.value.contains("Nat"), "{}", m.value),
            other => panic!("expected markup contents, got {other:?}"),
        }
    }

    #[test]
    fn goto_definition_resolves_a_constructor_to_its_defdata_span() {
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n(define one (the Nat Zero))";
        let doc = analyze(src, Path::new("."));
        let offset = src.rfind("(the Nat Zero)").unwrap() + "(the Nat ".len();
        let uri: Uri = "file:///tmp/test.bl".parse().unwrap();
        let resp = goto_definition_at(&doc, offset, &uri).expect("Zero is indexed");
        match resp {
            GotoDefinitionResponse::Scalar(loc) => {
                // The defdata form starts at byte 0, so line 0.
                assert_eq!(loc.range.start, Position::new(0, 0));
            }
            other => panic!("expected a scalar location, got {other:?}"),
        }
    }

    #[test]
    fn position_offset_roundtrip_is_utf16_aware() {
        let text = "(define x 1)\n(define y 2)";
        let newline = text.find('\n').unwrap();
        let pos = offset_to_position(text, newline + 1 + 8); // into "(define y" on line 2
        assert_eq!(pos.line, 1);
        assert_eq!(position_to_offset(text, pos), newline + 1 + 8);
    }

    // ---- E8 red: formatter + completion acceptance (un-ignore at the green flip) -------------

    #[test]
    fn lsp_formatting_returns_fmt_output() {
        let messy = "(  define a   1 )\n(define b 2)\n";
        let doc = analyze(messy, Path::new("."));
        let edits = formatting_edits(&doc).expect("a lexically well-formed buffer formats");
        let expected = blight_elab::format_source(messy).expect("the formatter accepts the buffer");
        assert_eq!(edits.len(), 1, "one whole-document edit: {edits:?}");
        assert_eq!(edits[0].new_text, expected);
        assert_eq!(edits[0].range.start, Position::new(0, 0));
        // Already-canonical text: an empty edit list, not a no-op whole-document rewrite (which
        // would churn editor undo history on every format-on-save).
        let canonical = analyze(&expected, Path::new("."));
        assert!(
            formatting_edits(&canonical)
                .expect("canonical text still formats")
                .is_empty(),
            "canonical text needs no edits"
        );
        // Lexically malformed text: no edits at all — never rewrite what cannot be re-read.
        let broken = analyze("(define a", Path::new("."));
        assert!(formatting_edits(&broken).is_none());
    }

    #[test]
    fn completion_lists_globals_and_keywords() {
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define plus-two (the Nat Zero))\n";
        let doc = analyze(src, Path::new("."));
        let items = completions_at(&doc, src.len());
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        // One representative per candidate class: a `define`d global, a constructor, the type
        // head, and surface keywords.
        for expected in ["plus-two", "Succ", "Nat", "define", "lam"] {
            assert!(
                labels.contains(&expected),
                "completion offers `{expected}`; got {labels:?}"
            );
        }
    }

    #[test]
    fn completion_lists_std_modules_after_load() {
        // The buffer is mid-keystroke (unterminated string), so `doc.definitions` is empty —
        // the `(load "` context must be detected lexically from the text before the cursor.
        let src = "(load \"";
        let doc = analyze(src, Path::new("."));
        let items = completions_at(&doc, src.len());
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(
            labels.contains(&"std/nat.bl"),
            "load-string completion offers the embedded std modules; got {labels:?}"
        );
        // Inside the load string, bare keywords are noise — the paths must not drown in them.
        assert!(
            !labels.contains(&"define"),
            "no keyword candidates inside a load string: {labels:?}"
        );
    }
}
