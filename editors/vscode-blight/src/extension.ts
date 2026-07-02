// Activates the Blight LSP client (Wave 1 / A1b of the roadmap). The server itself
// (`blight-lsp`, built from `crates/blight-lsp`) drives the same in-process elaboration pipeline
// as the CLI/REPL, so diagnostics here never drift from `blight build`.
//
// Scope today: whole-buffer diagnostics, hover (globals only — see the server's module doc for
// why locally-bound variables are out of scope), and go-to-definition over a form-head span
// index. Inline sub-expression squiggles, completion, and rename are deliberately not yet
// implemented server-side; see docs/roadmap-post-m6.md's Wave 1 / A1 gotcha ledger.

import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext): void {
  const config = vscode.workspace.getConfiguration("blight");
  const command = config.get<string>("serverPath", "blight-lsp");

  const serverOptions: ServerOptions = {
    command,
    args: [],
    transport: TransportKind.stdio,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "blight" }],
    outputChannelName: "Blight Language Server",
  };

  client = new LanguageClient(
    "blight-lsp",
    "Blight Language Server",
    serverOptions,
    clientOptions,
  );

  client.start().catch((err: unknown) => {
    vscode.window.showErrorMessage(
      `Blight: failed to start "${command}" — build it with ` +
        "`cargo build -p blight-lsp` (or set `blight.serverPath` in settings) " +
        `and reload the window. (${String(err)})`,
    );
  });

  context.subscriptions.push({
    dispose: () => {
      void client?.stop();
    },
  });
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
