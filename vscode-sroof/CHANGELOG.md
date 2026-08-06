# Changelog

## [0.7.0] — 2026-08-06

### Changed
- Version bump for the v0.7 release. The extension is unchanged; v0.7 adds
  generic enums and induction over parameterised inductive types.

## [0.6.0] — 2026-08-06

### Changed
- Version bump for the v0.6 release. The extension is unchanged; v0.6 adds the
  `have` tactic to the Scala 3 frontend.

## [0.5.0] — 2026-08-06

### Changed
- Version bump for the v0.5 release. The extension is unchanged; v0.5 adds
  generalized induction to the Scala 3 frontend, which the Scala compiler
  reports on directly.

## [0.4.0] — 2026-08-06

### Changed
- Version bump for the v0.4 release. The extension itself is unchanged; v0.4
  widens the Scala 3 frontend, which the Scala compiler reports on directly.

## [0.3.0] — 2026-08-06

### Changed
- Version bump for the v0.3 release.

### Notes
- The extension continues to serve the `.sroof` language. Verification of
  ordinary `.scala` sources, added in v0.3, happens inside the Scala compiler
  and is surfaced by whatever tooling already reports Scala compiler
  diagnostics — no extension support is required for it.

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
