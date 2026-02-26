/**
 * LSP server stub for the sproof theorem prover.
 *
 * This is a minimal stub that can be expanded later to provide full
 * language server functionality (diagnostics, go-to-definition, etc.)
 * once the sproof CLI exposes a JSON-RPC interface.
 *
 * Currently wired up as a stub only; the extension's hover provider in
 * extension.ts handles basic keyword documentation directly via the VS Code
 * extension API without needing a separate process.
 */

import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  InitializeResult,
  TextDocumentSyncKind,
  HoverParams,
  Hover,
  MarkupKind,
} from 'vscode-languageserver/node';

import { TextDocument } from 'vscode-languageserver-textdocument';

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);

connection.onInitialize((_params: InitializeParams): InitializeResult => {
  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
      hoverProvider: true,
    },
    serverInfo: {
      name: 'sproof-language-server',
      version: '0.1.0',
    },
  };
});

const KEYWORD_HOVER: Record<string, string> = {
  inductive: 'Define an inductive data type',
  def: 'Define a function',
  defspec: 'Define a theorem with a proof program',
  match: 'Pattern match on an inductive type',
  by: 'Begin a tactic proof',
  program: 'Mark a proof as a program (used with defspec)',
  fun: 'Lambda abstraction',
  trivial: 'Close a goal by reflexivity (NbE normalization)',
  triv: 'Alias for `trivial`',
  assume: 'Introduce a Pi-bound variable into context',
  apply: 'Apply a lemma or hypothesis to the current goal',
  simplify: 'Normalize the goal using NbE and close if equal',
  simp: 'Alias for `simplify`',
  induction: 'Perform structural induction on a value',
  induct: 'Alias for `induction`',
  sorry: '**Warning**: Incomplete proof placeholder — acts as an admitted axiom',
  have: 'Introduce an intermediate lemma into the proof context',
  Type: 'The universe of types (Type0)',
  Pi: 'Dependent function type Pi(x: A, B)',
  case: 'Constructor branch in an inductive definition or match expression',
};

connection.onHover((params: HoverParams): Hover | null => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) {
    return null;
  }

  const text = doc.getText();
  const offset = doc.offsetAt(params.position);

  // Find word boundaries around cursor
  let start = offset;
  let end = offset;
  while (start > 0 && /[A-Za-z0-9_]/.test(text[start - 1])) {
    start--;
  }
  while (end < text.length && /[A-Za-z0-9_]/.test(text[end])) {
    end++;
  }

  const word = text.slice(start, end);
  const description = KEYWORD_HOVER[word];

  if (description) {
    return {
      contents: {
        kind: MarkupKind.Markdown,
        value: `**sproof** — ${description}`,
      },
    };
  }

  return null;
});

documents.listen(connection);
connection.listen();
