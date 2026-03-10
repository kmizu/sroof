# Changelog

## [0.2.0] — 2026-03-02

### Added
- Goal/subgoal visualization command: `sroof: Show Goals`
- `sroof goals` output panel integration
- Automatic goal refresh on save for `.sroof` files
- Structured diagnostics integration via `sroof check --json`
- Problems panel support with source ranges and expected/actual type details

### Changed
- Version bump for the v0.2 release.
- Documentation refresh for release packaging flow.

## [0.1.0] — 2026-02-26

### Added
- Syntax highlighting for `.sroof` files via TextMate grammar
  - Keywords: `inductive`, `def`, `defspec`, `case`, `match`, `by`, `program`, `fun`
  - Tactic keywords: `trivial`, `triv`, `assume`, `apply`, `simplify`, `simp`, `induction`, `sorry`, `have`, `calc`, `ring`
  - Type keywords: `Type`, `Type0`, `Type1`, `Type2`, `Pi`
  - Operators, comments, numbers, qualified constructor names
- Language configuration (bracket matching, comment toggling, auto-indent)
- Snippets for common patterns (inductive types, theorems, tactics)
- Hover documentation for all sroof keywords
- Document outline showing `def`, `defspec`, and `inductive` definitions
- LSP server stub (ready for future expansion)
