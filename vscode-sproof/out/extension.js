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
function activate(context) {
    console.log('sproof extension activated');
    const hoverProvider = vscode.languages.registerHoverProvider('sproof', {
        provideHover(document, position) {
            const wordRange = document.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
            if (!wordRange) {
                return null;
            }
            const word = document.getText(wordRange);
            const doc = KEYWORD_DOCS[word];
            if (doc) {
                const md = new vscode.MarkdownString(`**sproof** — ${doc}`);
                md.isTrusted = true;
                return new vscode.Hover(md, wordRange);
            }
            return null;
        }
    });
    // Register a document symbol provider so the outline shows defs/defspecs
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
    context.subscriptions.push(hoverProvider, symbolProvider);
}
function deactivate() { }
//# sourceMappingURL=extension.js.map