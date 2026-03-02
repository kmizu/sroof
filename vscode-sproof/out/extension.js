"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = __importStar(require("vscode"));
const fs = __importStar(require("fs"));
const os = __importStar(require("os"));
const path = __importStar(require("path"));
const child_process_1 = require("child_process");
const KEYWORD_DOCS = {
    'inductive': 'Define an inductive data type.\n\nExample:\n```sproof\ninductive Nat {\n  case zero: Nat\n  case succ(n: Nat): Nat\n}\n```',
    'def': 'Define a function.\n\nExample:\n```sproof\ndef add(n: Nat, m: Nat): Nat = match n {\n  case Nat.zero => m\n  case Nat.succ k => Nat.succ(add(k, m))\n}\n```',
    'defspec': 'Define a theorem together with its proof.\n\nExample:\n```sproof\ndefspec add_zero(n: Nat): add(n, Nat.zero) = n program = {\n  by induction n { ... }\n}\n```',
    'match': 'Eliminate an inductive type by pattern matching.\n\nExample:\n```sproof\nmatch n {\n  case Nat.zero => ...\n  case Nat.succ k => ...\n}\n```',
    'by': 'Introduce a tactic proof block.',
    'program': 'Mark a definition as a proof program (used in `defspec`).',
    'fun': 'Lambda abstraction (anonymous function).\n\nExample:\n```sproof\nfun x: Nat => Nat.succ(x)\n```',
    'trivial': 'Close a goal that holds by reflexivity (both sides normalize to the same term).',
    'triv': 'Alias for `trivial`.',
    'assume': 'Introduce a Pi-bound variable into the local context.\n\nExample:\n```sproof\nassume n: Nat\n```',
    'apply': 'Apply a previously proved lemma or hypothesis to transform the current goal.',
    'simplify': 'Normalize both sides of the goal using NbE (Normalization by Evaluation) and close if equal.',
    'simp': 'Alias for `simplify`.',
    'induction': 'Perform structural induction on an inductive type.\n\nExample:\n```sproof\ninduction n {\n  case zero => trivial\n  case succ k => ...\n}\n```',
    'induct': 'Alias for `induction`.',
    'sorry': '**Warning**: Placeholder for an incomplete proof. Acts as an axiom and should be removed before considering a proof complete.',
    'have': 'Introduce an intermediate result (local lemma) into the proof context.',
    'calc': 'Equational reasoning: chain equalities step by step.',
    'ring': 'Discharge ring-equational goals automatically.',
    'Type': 'The universe of types. `Type` is `Type0`. Subtypes: `Type0`, `Type1`, `Type2`.',
    'Type0': 'The base universe of small types.',
    'Type1': 'The universe containing `Type0`.',
    'Type2': 'The universe containing `Type1`.',
    'Pi': 'Dependent function type `Pi(x: A, B)`, where `B` may mention `x`.',
    'case': 'Introduces a constructor in an inductive type definition or a branch in a match expression.',
};
function extractProofState(output) {
    const start = output.indexOf('(proof-state');
    if (start < 0) {
        return null;
    }
    let depth = 0;
    let inString = false;
    let escaped = false;
    for (let i = start; i < output.length; i++) {
        const ch = output[i];
        if (inString) {
            if (escaped) {
                escaped = false;
            }
            else if (ch === '\\') {
                escaped = true;
            }
            else if (ch === '"') {
                inString = false;
            }
            continue;
        }
        if (ch === '"') {
            inString = true;
            continue;
        }
        if (ch === '(') {
            depth++;
        }
        else if (ch === ')') {
            depth--;
            if (depth === 0) {
                return output.slice(start, i + 1);
            }
        }
    }
    return output.slice(start);
}
function formatProofState(proofState) {
    return proofState
        .replace(/\)\s+\(/g, ')\n(')
        .replace(/\(goal\b/g, '\n(goal')
        .trim();
}
function extractJsonPayload(output) {
    const lines = output.split(/\r?\n/).map(line => line.trim()).filter(line => line.length > 0);
    for (let i = lines.length - 1; i >= 0; i--) {
        const line = lines[i];
        if (line.startsWith('{') && line.endsWith('}')) {
            return line;
        }
    }
    return null;
}
function clampPosition(document, line, column) {
    const maxLine = Math.max(0, document.lineCount - 1);
    const clampedLine = Math.max(0, Math.min(line, maxLine));
    const maxChar = document.lineAt(clampedLine).text.length;
    const clampedChar = Math.max(0, Math.min(column, maxChar));
    return new vscode.Position(clampedLine, clampedChar);
}
function toRange(document, range) {
    const startLine = Math.max(0, ((range?.start?.line ?? 1) - 1));
    const startCol = Math.max(0, ((range?.start?.column ?? 1) - 1));
    const endLine = Math.max(startLine, ((range?.end?.line ?? (startLine + 1)) - 1));
    const rawEndCol = Math.max(startCol + 1, ((range?.end?.column ?? (startCol + 2)) - 1));
    const start = clampPosition(document, startLine, startCol);
    const end = clampPosition(document, endLine, rawEndCol);
    return new vscode.Range(start, end);
}
function toMessage(d) {
    const lines = [];
    lines.push(d.message ?? 'sproof check failed');
    if (d.expected) {
        lines.push(`expected: ${d.expected}`);
    }
    if (d.actual) {
        lines.push(`actual:   ${d.actual}`);
    }
    if (d.hint) {
        lines.push(`hint:     ${d.hint}`);
    }
    return lines.join('\n');
}
async function refreshDiagnostics(document, collection) {
    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = workspaceFolder ? workspaceFolder.uri.fsPath : path.dirname(document.uri.fsPath);
    const escapedPath = document.uri.fsPath.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
    const commandArg = `cli/run check --json "${escapedPath}"`;
    const output = await new Promise((resolve) => {
        (0, child_process_1.execFile)('sbt', [commandArg], { cwd, timeout: 120000 }, (err, stdout, stderr) => {
            resolve((stdout ?? '') + '\n' + (stderr ?? '') + (err ? `\n${String(err)}` : ''));
        });
    });
    const jsonPayload = extractJsonPayload(output);
    if (!jsonPayload) {
        return;
    }
    try {
        const parsed = JSON.parse(jsonPayload);
        if (parsed.ok) {
            collection.delete(document.uri);
            return;
        }
        const diagnostics = (parsed.diagnostics ?? []).map((d) => {
            const diagnostic = new vscode.Diagnostic(toRange(document, d.range), toMessage(d), vscode.DiagnosticSeverity.Error);
            diagnostic.source = 'sproof';
            diagnostic.code = d.code ?? d.phase ?? 'error';
            return diagnostic;
        });
        if (diagnostics.length === 0) {
            const fallback = new vscode.Diagnostic(toRange(document), parsed.error ?? 'sproof check failed', vscode.DiagnosticSeverity.Error);
            fallback.source = 'sproof';
            fallback.code = 'error';
            collection.set(document.uri, [fallback]);
        }
        else {
            collection.set(document.uri, diagnostics);
        }
    }
    catch {
        // Ignore malformed output from command execution.
    }
}
async function runCheckAndShowGoals(document, channel, reveal, latestRunByDocument) {
    const documentKey = document.uri.toString();
    const runId = (latestRunByDocument.get(documentKey) ?? 0) + 1;
    latestRunByDocument.set(documentKey, runId);
    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = workspaceFolder ? workspaceFolder.uri.fsPath : path.dirname(document.uri.fsPath);
    const tmpPath = path.join(os.tmpdir(), `sproof-goals-${Date.now()}-${Math.random().toString(16).slice(2)}.sproof`);
    fs.writeFileSync(tmpPath, document.getText(), 'utf8');
    const commandArg = `cli/run check ${tmpPath}`;
    const output = await new Promise((resolve) => {
        (0, child_process_1.execFile)('sbt', [commandArg], { cwd, timeout: 120000 }, (err, stdout, stderr) => {
            resolve((stdout ?? '') + '\n' + (stderr ?? '') + (err ? `\n${String(err)}` : ''));
        });
    });
    try {
        fs.unlinkSync(tmpPath);
    }
    catch {
        // best-effort cleanup
    }
    if (latestRunByDocument.get(documentKey) !== runId) {
        return;
    }
    const proofState = extractProofState(output);
    channel.clear();
    if (proofState) {
        channel.appendLine(`Current goals for: ${document.fileName}`);
        channel.appendLine('');
        channel.appendLine(formatProofState(proofState));
        if (reveal) {
            channel.show(true);
        }
        return;
    }
    const ok = output.includes('OK:');
    if (ok) {
        channel.appendLine(`No open goals: ${document.fileName}`);
    }
    else {
        channel.appendLine(`Could not extract proof-state for: ${document.fileName}`);
        channel.appendLine('');
        channel.appendLine(output.trim());
    }
    if (reveal) {
        channel.show(true);
    }
}
function activate(context) {
    console.log('sproof extension activated');
    const goalChannel = vscode.window.createOutputChannel('sproof goals');
    const latestRunByDocument = new Map();
    const diagnosticCollection = vscode.languages.createDiagnosticCollection('sproof');
    const hoverProvider = vscode.languages.registerHoverProvider('sproof', {
        provideHover(document, position) {
            const wordRange = document.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
            if (!wordRange) {
                return null;
            }
            const word = document.getText(wordRange);
            const doc = KEYWORD_DOCS[word];
            if (doc) {
                const md = new vscode.MarkdownString(`**sproof** - ${doc}`);
                md.isTrusted = true;
                return new vscode.Hover(md, wordRange);
            }
            return null;
        }
    });
    const symbolProvider = vscode.languages.registerDocumentSymbolProvider('sproof', {
        provideDocumentSymbols(document) {
            const symbols = [];
            const defPattern = /^\s*(def|defspec|inductive)\s+([A-Za-z_][A-Za-z0-9_]*)/gm;
            const text = document.getText();
            let match;
            while ((match = defPattern.exec(text)) !== null) {
                const keyword = match[1];
                const name = match[2];
                const startPos = document.positionAt(match.index);
                const endPos = document.positionAt(match.index + match[0].length);
                const range = new vscode.Range(startPos, endPos);
                let kind;
                switch (keyword) {
                    case 'inductive':
                        kind = vscode.SymbolKind.Class;
                        break;
                    case 'defspec':
                        kind = vscode.SymbolKind.Interface;
                        break;
                    default:
                        kind = vscode.SymbolKind.Function;
                }
                symbols.push(new vscode.DocumentSymbol(name, keyword, kind, range, range));
            }
            return symbols;
        }
    });
    const showGoalsCommand = vscode.commands.registerCommand('sproof.showGoals', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || editor.document.languageId !== 'sproof') {
            vscode.window.showInformationMessage('Open a .sproof file to show current goals.');
            return;
        }
        await runCheckAndShowGoals(editor.document, goalChannel, true, latestRunByDocument);
    });
    const saveWatcher = vscode.workspace.onDidSaveTextDocument(async (doc) => {
        if (doc.languageId !== 'sproof') {
            return;
        }
        await runCheckAndShowGoals(doc, goalChannel, false, latestRunByDocument);
        await refreshDiagnostics(doc, diagnosticCollection);
    });
    const closeWatcher = vscode.workspace.onDidCloseTextDocument((doc) => {
        latestRunByDocument.delete(doc.uri.toString());
        diagnosticCollection.delete(doc.uri);
    });
    context.subscriptions.push(hoverProvider, symbolProvider, showGoalsCommand, saveWatcher, closeWatcher, goalChannel, diagnosticCollection);
}
function deactivate() { }
//# sourceMappingURL=extension.js.map