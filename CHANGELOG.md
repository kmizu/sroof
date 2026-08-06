# Changelog

## [0.8.0] - 2026-08-07

Groundwork for the two items v0.7 left outstanding: publishing is ready but for
credentials, and indexed families now parse and are recorded.

### Added — indexed families, steps 1 and 2
- **A constructor's return type may carry index arguments.**
  `case vnil: Vec(A)(Nat.zero)` was a parse error until now: `typeVarOrApp`
  accepted exactly one application group. It accepts any number and flattens
  them, so `Vec(A)(n)` and `Vec(A, n)` denote the same applied type — which
  arguments are parameters and which are indices is decided by the declaration,
  not by where the parentheses fall.
- **`CtorDef.retIndices` is populated.** It was a field nothing wrote. The
  elaborator now fills it from the declared return type, in the scope the last
  argument type sees, so an index may mention the constructor's own arguments.

  Both are backward compatible: a return type that is not an application of the
  inductive being declared, or that has the wrong argument count, yields `Nil` —
  exactly the previous behaviour. Every existing declaration means what it meant,
  and all 590 tests pass unchanged.

  **Indices still carry no information.** Steps 1 and 2 record them; the checker
  does not yet read them. `Vec.nil` and `Vec.cons(...)` still have the same type.
  See below.

### Attempted and reverted — indexed families, step 3
`IndChecker.inferCon` was extended to apply a constructor's `retIndices`, which
is what would finally make an index real. It passed all 590 tests — the change is
inert while `retIndices` is empty, which it is everywhere today — but
`#check Vec.vcons(...)` failed with `Unbound De Bruijn index 2`.

It was reverted rather than shipped. `inferCon` is inside the TCB for logical
validity, and an unvalidated change there is exactly what this project has
declined to ship in v0.5 and v0.6. `docs/indexed-families.md` records the two
obstacles the attempt uncovered — parameter inference is a documented heuristic
with nothing to work from for a nullary constructor, and `instantiateArgType`'s
ordering doc disagrees with its call site — so the next attempt starts informed.

### Added — publishing
- **Maven Central publishing is configured.** POM metadata (licence, SCM,
  developers, homepage — all of which Central rejects an artifact for missing),
  Sonatype wiring, `sbt-sonatype` and `sbt-pgp`, credentials read from the
  environment for CI, and a `ci-release-sroof` alias. `docs/publishing.md` says
  what to obtain and where to put it; `.github/workflows/release.yml` releases on
  a pushed `v*` tag and skips green when the secrets are absent, so an
  unconfigured repository or a fork is unaffected.

  Verified by `publishLocal`: `sroof-scala-api`, `sroof-scala-frontend`, and
  `sroof-scala-plugin` produce jar, sources, javadoc, and pom. Only credentials
  are missing.

  The groupId is `io.github.kmizu`, which Central verifies via the GitHub account
  of the same name. `io.sroof` would additionally need DNS verification of
  `sroof.io`; it is one value in `build.sbt`, and nothing is published yet, so
  switching costs nothing today.

### Documented
- **Indexed families are not implemented, contrary to appearances.**
  `docs/indexed-families.md` records the investigation. `IndDef.indices` is
  populated, but `CtorDef.retIndices` is a field **nothing writes or reads**, and
  a constructor's declared return type is parsed and discarded (`SCtor.retTpe`
  has no readers anywhere). The parser cannot even express
  `case vnil: Vec(A)(Nat.zero)`.

  So `stdlib/Vec.sroof` writing the bare `Vec` is not a convention to follow —
  it is the only thing that parses, and the `n: Nat` index is phantom:
  `Vec.nil` and `Vec.cons(...)` have the same type, and nothing about lengths can
  be stated. The file now says so.

  v0.7's fix does not extend to this. A type parameter has the same value in
  every constructor, so one uniform substitution sufficed; an index differs per
  constructor, so the motive must abstract over it and each branch must
  specialise it. The work starts in the parser and runs through the elaborator,
  checker, and tactic engine before any frontend work is meaningful.

## [0.7.0] - 2026-08-06

Lifts the limitation that had been recorded in `stdlib/PolyList.sroof` since the
polymorphic list was written: **induction over parameterised inductive types**.
That fix lives in the shared tactic engine, so it lands on both frontends at
once, and it is what made generic enums possible in the Scala path.

### Fixed (tactic engine, benefits both frontends)
- **Induction over a parameterised inductive.** `Builtins.buildFixCase` extended
  a branch's context with the constructor's **raw** argument types, which still
  mention the inductive's type parameters — indices that are bound nowhere in a
  branch context and silently pointed at `_rec` and `_n` instead. The scrutinee's
  type arguments are now substituted in first.
- **The branch context was based on the wrong context.** It dropped the induction
  variable while the proof term is placed in the goal's context. Those agree only
  when every entry a branch mentions is *newer* than the induction variable —
  true for the common shapes, which is why it went unnoticed, and false as soon
  as a type parameter is declared before the value being inducted on. Both are
  now stated in the goal's context.
- `Fix`'s body embeds the scrutinee's type inside its own binder, so that type
  needs shifting. It is the identity for a monomorphic (closed) type, which hid
  the problem.

### Added
- **Generic enums in the Scala frontend.** `enum Lst[A]`, definitions and
  theorems with type parameters, and induction over them:
  ```scala
  @theorem
  def appendAssoc[A](xs: Lst[A], ys: Lst[A], zs: Lst[A]): Proof =
    prove(append(append(xs, ys), zs) === append(xs, append(ys, zs)))(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      })
  ```
- **Worked examples of elementary mathematics.** `examples-scala3/Arithmetic.scala`
  proves the Peano addition and multiplication laws — the defining equations,
  their mirrors, and associativity — in the order a textbook would build them.
  `examples-scala3/Lists.scala` proves the list laws over a generic list,
  including that `length` distributes over `append`. Both are compiled with the
  plugin, so they are checked, not illustrative.
- `stdlib/PolyList.sroof` gains the inductive proofs its header used to say were
  impossible, and the header now explains the convention that makes them work.

### Changed
- `IndChecker.instantiateCtorArgTpe` and `extractIndParams` are public, so the
  tactic engine can reuse the checker's definition of the constructor-argument
  convention instead of restating it.

### Unchanged
- The trusted kernel. Every proof, generic or not, still goes through
  `Kernel.verify`.


## [0.6.0] - 2026-08-06

Adds `have`, so a proof can be written in steps, and converts another batch of
documented-but-untested claims into tested ones.

### Added
- **`have(claim)(proof) { h => ... }`** — prove an intermediate equation, bind it
  as `h`, and continue with it in scope. The claim becomes a goal in its own
  right, so `have` cannot be used to assume something convenient: an unprovable
  claim fails the theorem.

### Tested, not merely claimed
Two new suites compile constructs that were reachable by reading the extractor
but exercised by nothing:

- **Branch reordering.** `Term.Mat` matches branches to constructors *by
  position*, so a wrong normalisation would have produced a proof about the wrong
  branches rather than a failure. Out-of-order `match` and `induction` branches
  are now pinned.
- Two `@proofModule` objects in one file, a failure in the second still failing
  the compilation, enums with more than two cases, transitive inlining across a
  chain of definitions, `simplify` citing several verified theorems at once, and
  deeply nested constructor expressions.

All passed, so this release found no new defects there — unlike v0.5, where the
same exercise uncovered two.

### Documented
- **A second blocker under generic enums.** v0.5 identified
  `Builtins.buildFixCase` as the obstacle. Attempting the fix and running an
  inductive proof over `PolyList` surfaced another one underneath: the *bare*
  `Ind("PolyList")` written in stdlib definition signatures does not match the
  *applied* `App(Ind("PolyList"), A)` that a constructor field carries.
  Instantiating argument types does not reconcile those. `docs/scala3-frontend.md`
  §11 now records the required order of work, and why steps 1–2 are shared-code
  changes deserving their own milestone rather than a corner of a mixed release.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.

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

