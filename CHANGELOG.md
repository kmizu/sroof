# Changelog

## [0.5.0] - 2026-08-06

Adds generalized induction — the first release to increase what the Scala path
can *prove*, rather than only what it can parse — and turns several documented
claims into tested ones.

### Added
- **`inductionGeneralizing(x, y, ...)`** — induction whose hypothesis is
  universally quantified over the other named parameters. Needed whenever those
  parameters change as the recursion proceeds, since a hypothesis fixed at their
  original values says nothing about the recursive call.
- **`exactIh(k)(at...)`** — closes the goal with that hypothesis, instantiated at
  the given values. Its arguments are expressions, not just names, because the
  interesting instantiations are at changed values (`Succ(acc)`).
- **References to parameterless definitions.** `def two: Nat = ...` could be
  declared but not used: a nullary reference arrives with no enclosing `Apply`,
  and fell through to "neither a binder nor a constructor".

### Fixed
- A parameterless definition was `Fix`-wrapped like any other. A nullary `Fix`
  can never reduce — it only unfolds when applied — so wherever it was inlined it
  sat unevaluated, and the evaluator failed on it. Parameterless definitions now
  translate to their body directly, matching the legacy elaborator, and nullary
  self-recursion is rejected with a diagnostic rather than left dangling.
- `mentionsIh` did not count `exactIh` as a use of the hypothesis, which would
  have meant the branch never requested one.

### Changed
- The `ih` diagnostics are now produced in one place and shared by `ih` and
  `exactIh`, so the two cannot drift apart. Wording changed slightly.
- The generic-enum rejection now explains *why*, and
  `docs/scala3-frontend.md` §11 records the real blocker (see below).

### Documented
- **Generic enums are blocked below the frontend, not in it.** Earlier drafts
  implied the work was frontend-side. In fact the core already represents
  parameterised inductives; what fails is induction over them, because
  `Builtins.buildFixCase` extends a branch context with raw constructor argument
  types that still mention the type parameters. `stdlib/PolyList.sroof` records
  the same limitation on the `.sroof` side. Supporting generics in the frontend
  alone would give generic declarations with no way to prove anything inductive
  about them; the fix belongs in `Builtins` and benefits both frontends.

### Tested, not merely claimed
A new suite pins constructs the subset table asserted but nothing exercised:
inferred local `val` types, `new Ctor(...)`, enum cases with explicit `extends`,
matching on a call result, multi-field non-recursive constructors, all-wildcard
patterns, mutually referring enums, and parameterless definitions — the last of
which turned out to be broken.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.

## [0.4.0] - 2026-08-06

Widens the Scala subset the compiler plugin accepts, and tightens the parts that
were already there.

### Added
- **Curried parameter lists.** `def f(a: A)(b: B)` and `@theorem def t(a: A)(b: B)`
  are supported. Lists are flattened — core types are curried anyway — and call
  sites are checked against the flattened arity, so partial application is
  rejected rather than silently accepted.
- **Runs of local `val`s.** A verified definition may now open with several
  immutable bindings, each visible to the next, instead of exactly one.
- **Recursive fields after other fields.** An induction hypothesis is generated
  whenever a constructor's *last* field has the inductive's own type, so
  `Cons(tag: Tag, rest: Tagged)` now supports `ih(rest)`. Previously only
  single-field constructors qualified.
- **`cases(x) { ... }`** — constructor split with no induction hypothesis. `ih`
  inside it is rejected with a message pointing at `induction`.
- **`rewrite(equations*)`** — applies equations as directed rewrites, alongside
  `simplify`'s normalise-then-close.

### Fixed
- The induction hypothesis was located by taking the head of an unordered map of
  pattern binders. With single-field constructors that happened to be correct;
  with the multi-field constructors this release accepts, it would have bound the
  hypothesis to an arbitrary field. It is now looked up by binder identity
  against the constructor's last field.
- `ih` on an unnamed (`_`) recursive field reported "no recursive field"; it now
  asks for the field to be bound to a name.
- The diagnostic for an unsupported block still claimed only a single `val` was
  allowed.

### Changed
- `docs/scala3-frontend.md`, both READMEs, and the normative example reflect the
  wider subset. The example now also demonstrates `cases`, curried theorem
  parameters, and `@simp` feeding a bare `simplify()`.
- Future work now records *why* generic enums are deferred rather than merely
  that they are: they touch the trusted translation layer at several points at
  once, and belong in their own milestone with per-construct golden tests.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.



## [0.3.0] - 2026-08-06

The release that changes what sroof *is*: a Scala 3 verification system with an
independent proof kernel, rather than a separate Scala-like language.

### Added
- **Scala 3 frontend.** Theorems can now be stated and proved in ordinary
  `.scala` files, verified during compilation by a standard Scala 3 compiler
  plugin. Five new modules: `scala-api`, `scala-frontend`, `scala-plugin`,
  `examples-scala3`, `scala-it`.
- `sroof.annotation` markers (`@proofModule`, `@theorem`, `@simp`) and the
  `sroof.lang` DSL (`===`, `prove`, `trivial`, `induction`, `ih`, `simplify`).
  All proof values erase to inert `Unit`; nothing runs at runtime.
- A dotc-independent resolved IR and a Scala-to-core translation layer, so the
  translation, proof, and kernel layers stay portable across compiler versions.
- `docs/scala3-frontend.md`: motivation, architecture, the exact supported and
  unsupported subsets, translation rules, and the migration plan.
- `Eq.mkPropType`, a single definition of the propositional-equality encoding
  used for goals.
- CI job `scala-frontend`: frontend tests, plugin-enabled example compilation,
  runtime tests, and integration tests that invoke `dotc` for real.

### Changed
- `docs/trust-model.md` now separates two claims: **core logical validity**
  (decided by the kernel, unchanged) and **Scala semantic correspondence** (the
  claim that the core model *is* the Scala program). The Scala-to-core bridge is
  inside the TCB for the second claim, and the document says so plainly.
- `README.md` / `README-ja.md`: added the Scala 3 path, and corrected the tactic
  reference to match the implementation.
- `sbt-sroof` is documented as legacy `.sroof` integration, with the design for a
  future compiler-plugin mode recorded but deliberately not implemented.

### Fixed
- The tactic reference listed `ring` and the alias `induct`, neither of which
  exists in the parser, and conflated `assumption` with `assume`. The tables now
  match the implementation and cover the full tactic set.
- Documentation gave the native binary as `sroof-cli-native-out`; the build
  produces `sroof-cli-native`.

### Unchanged
- The `.sroof` language, parser, elaborator, CLI, extractor, stdlib, examples,
  VS Code extension, sbt plugin, and Scala Native binary all behave exactly as in
  v0.2. This is a supported legacy path, not a deprecated one.
- **The trusted kernel is byte-for-byte unchanged**, and no kernel test was
  weakened.

### Known limitations
- The Scala 3 frontend supports a deliberately narrow subset: non-generic enums,
  single-parameter-list pure `def`s over them, structural self-recursion,
  exhaustive matches, immutable local `val`s, equality goals, and the tactics
  `trivial`, `induction`, `ih`, `simplify`. Everything else is rejected with a
  diagnostic rather than approximated.
- `ih` requires a constructor with exactly one field of its own inductive type,
  and a pattern binder may not be named `ih`.
- Lemma reuse on the Scala path is limited to theorems verified earlier in the
  same module; there is no cross-compilation-unit proof metadata yet.
- `sorry` remains available on the `.sroof` path as an explicit unsound
  placeholder. The Scala path has no equivalent and never had one.

## [0.2.0] - 2026-03-02

### Added
- Richer tactic and proof authoring support in examples (`nat`, `int`, `list`, `vec`).
- Proof-state S-expression output on proof failures for tooling/LLM consumption.
- JSON output mode for `check --json`.
- VS Code extension with syntax highlighting, snippets, hover docs, and outline support.
- Scala Native build + CI smoke-test workflow.

### Changed
- Updated release documentation and v0.2 release checklist.
- Refined `examples/vec.sroof` to satisfy structural recursion checks.

### Known limitations
- Some advanced recursive patterns still require argument ordering that is friendly to the structural termination checker.
- `sorry` remains available as an explicit unsound placeholder and should not be used in production proofs.

