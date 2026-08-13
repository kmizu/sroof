# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is sroof?

A dependently-typed theorem prover (proof assistant) written in Scala 3. Uses a predicative Calculus of Inductive Constructions (CIC).

There are **two frontends** over one shared core and kernel:

1. **Scala 3 frontend** (`scala-api`, `scala-frontend`, `scala-plugin`) — the new primary path. Users write ordinary `.scala` files with `@proofModule`/`@theorem` annotations; a standard Scala 3 compiler plugin translates a restricted pure subset into core terms, runs the existing tactics, and gates every proof through `Kernel.verify`. Currently covers a deliberately narrow subset (see `docs/scala3-frontend.md`).
2. **`.sroof` language** (`syntax`, `cli`, `extract`) — the mature legacy path, with Scala-like brace syntax. Fully supported and unchanged; not deprecated.

When changing shared code (`core`, `eval`, `checker`, `tactic`, `kernel`), remember both frontends depend on it.

## Build & Test Commands

```bash
# Build (JVM)
sbt compile

# Run all tests
sbt test

# Run a single module's tests
sbt core/test
sbt cli/test
sbt tactic/test

# Run a single test suite by name
sbt "cli/testOnly sroof.TacticHintSuite"

# Check a proof file
sbt "cli/run check examples/nat.sroof"

# Check with JSON output (for tooling)
sbt "cli/run check --json examples/nat.sroof"

# Treat sorry as error (exit 1)
sbt "cli/run check --fail-on-sorry examples/nat.sroof"

# Auto-repair sorry proofs using the proof agent
sbt "cli/run agent examples/nat.sroof"

# Extract Scala 3 code from proofs
sbt "cli/run extract examples/nat.sroof"

# Start the interactive REPL
sbt "cli/run repl"

# Build native binary (requires clang, lld, libunwind-dev)
sbt cliNative/nativeLink
# Native binary location: ./cli-native/target/scala-3.3.6/sroof-cli-native

# Run all native tests (LLVM required)
sbt nativeRoot/test
```

### Scala 3 frontend

```bash
# Frontend unit + golden translation tests (no compiler involved)
sbt scalaFrontend/test

# Build the compiler plugin
sbt scalaPlugin/package

# Compile the normative example WITH the plugin enabled.
# A failing @theorem makes this command fail — that is the point.
sbt scalaExamples/compile

# Runtime tests proving the verified Scala is still an ordinary program
sbt scalaExamples/test

# Integration tests: real dotc invocations with the plugin (positive + negative)
sbt scalaIt/test
```

## Module Dependency Graph

```
cli (entry point: sroof.Main)
├── syntax (Parsley parser → SurfaceAst → Elaborator → core Terms)
│   └── core (Term ADT, De Bruijn indices, Context, GlobalEnv)
├── tactic (TacticM monad, built-in tactics, ProofState)
│   └── checker (bidirectional type checking)
│       └── eval (Normalization by Evaluation: Eval/Quote/Semantic)
│           └── core
├── extract (Scala 3 code generation, proof erasure)
│   └── checker
└── kernel (trusted kernel, <500 LOC, auditable)
    └── tactic
```

The Scala 3 frontend sits alongside, sharing the same core and kernel:

```
scala-plugin (StandardPlugin + PluginPhase; the only dotc-aware code)
└── scala-frontend (resolved IR → core Terms → tactics → Kernel.verify)
    └── kernel

scala-api      (annotations + DSL; depends on nothing but the Scala library)
examples-scala3 (real .scala compiled with -Xplugin; fails the build if a proof fails)
scala-it        (integration tests invoking dotc in-process)
```

Eight JVM modules + eight mirrored Scala Native modules, plus five Scala-frontend modules. Native modules have no source of their own — they share sources from JVM counterparts via `unmanagedSourceDirectories` in build.sbt. **The Scala-frontend modules are deliberately not mirrored into `nativeRoot`** (the plugin links against the JVM-only compiler).

Outside the sbt build: `vscode-sroof/` (VS Code extension: `npm ci && npm run compile`), `sbt-sroof/` (sbt plugin, Scala 2.12, legacy `.sroof` integration), `benchmarks/` + `scripts/benchmark.py` (perf suite used by CI), `docs/` (scala3-frontend, proof-cookbook, trust-model, json-schema, effects, stdlib, lemma-bundles).

Note: in `build.sbt` the `eval` directory's project variable is named `nbe` (so `sbt nbeNative/compile` etc.), but the sbt task prefix follows the directory name: `sbt eval/test`.

## Key Architecture Concepts

**De Bruijn indices**: All variable binding uses De Bruijn indices (not named variables). `Subst.scala` in core handles substitution and shifting. Off-by-one errors in index manipulation are the most common source of bugs, especially in `Builtins.scala` induction/cases tactics.

**Term ADT** (`core/Term.scala`): `Var`, `App`, `Lam`, `Pi`, `Let`, `Uni`, `Ind`, `Con`, `Mat`, `Fix`, `Meta`. This is the internal representation after elaboration.

**NbE (Normalization by Evaluation)** (`eval/`): Three files — `Eval.scala` (reduce to WHNF), `Quote.scala` (semantic values → terms), `Semantic.scala` (value domain with closures and neutral terms).

**Bidirectional type checking** (`checker/Bidirectional.scala`): Inference mode and checking mode. `IndChecker.scala` validates inductive type definitions.

**TacticM monad** (`tactic/TacticM.scala`): Pure functional proof state management via `Either[TacticError, ?]`. Tactics manipulate a goal stack with context.

**Elaboration pipeline**: `.sroof` file → `Parser.scala` (Parsley combinators) → `SurfaceAst` → `Elaborator.scala` → core `Term`s + `GlobalEnv`. The `ElabResult` carries the `GlobalEnv` (inductives, defs, structures, operators, simpSet), elaborated def bodies, and `defspecs` (proposition + `SProof`).

**Checker pipeline** (`cli/Checker.scala`): `checkDefBodies` (every `def` body against its declared type, via `Kernel.verify` — added in v0.14; before that a `def` could say one thing and mean another), then Phase 1 (`generateProofCandidates`) runs tactics to produce proof terms, then Phase 2 (`finalizeProofCandidates`) passes every term through `Kernel.verify`. Tactics are untrusted generators; the kernel is the sole arbiter.

**`IndChecker` and `Bidirectional` are inside the TCB.** `Kernel.verify` delegates to `Bidirectional.check`, which calls straight into `IndChecker` — the kernel re-checks a proof *using* those rules, so it cannot catch a bug in them. `IndChecker`'s header used to claim the opposite. See `docs/trust-model.md`.

**`Eval` throws on terms it cannot reduce; that must never reach the user.** `Bidirectional.whnf`, `convCheck`, `Kernel.check`, and `Checker.executeProof` each catch it and turn it into a rejection. Every catch is rejection-safe by construction — an exception can lose a proof, never manufacture one.

**Incremental caching** (`Main.scala`): Three-level in-process caches (parse → elab → proof) keyed on MurmurHash3 of source/AST. Each cache layer is invalidated only when its upstream hash changes, enabling fast re-checks within the same JVM.

**Proof agent** (`cli/` — `TacticGen.scala`, `SearchLoop.scala`, `FileRepairer.scala`): BFS-style tactic search that auto-repairs `by sorry` placeholders. Generates candidates ordered by success probability (depth-0: trivial/assumption/simplify, depth-1: induction).

**GlobalEnv extensions**: Beyond inductives and defs, `GlobalEnv` tracks `structures` (record types, desugared to single-constructor inductives + field accessor defs), `operators` (symbol → def name, no overloading), and `simpSet` (def names tagged `@[simp]` for the `simplify` tactic's default lemma set).

## sroof Language Syntax

```scala
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

Built-in tactics (full set in `syntax/Parser.scala` tactic parser):
- Closers: `trivial` (alias `triv`), `rfl`, `decide`, `assumption`, `contradiction`, `tauto`, `sorry`, `skip`
- Intro/apply: `assume x ...` (aliases `intro`/`intros`), `apply f`, `exact e`
- Rewriting: `simplify [lemmas]` (alias `simp`), `rewrite [h]` (alias `rw`)
- Case analysis: `induction x { cases }` (supports `induction x generalizing y z { ... }`), `cases x { cases }`
- Structure: `have h : T = { proof }; cont`, `calc { chain }`, `{ t1; t2 }` sequencing
- Logic: `split`, `constructor`, `left`, `right`, `use e` (alias `exists`), `by_contra h`, `obtain [x y] from h`, `specialize h arg`
- Combinators: `try t`, `first | t1 | t2`, `repeat t`, `all_goals t`

There is no `ring` tactic (removed; use `simplify`/`calc`).

Additional language features:
- Scala 3-style aliases: `theorem` = `defspec`, `enum` = `inductive`, `trait` = `structure`, `given` = `instance`
- `structure Name { field: Type ... }` — record types (desugared to inductive + field accessor defs)
- `instance name: StructName { field = expr ... }` — record values with named field bindings (typeclass-style; see `examples/typeclass.sroof`)
- `@[simp] def ...` — marks a def as a default simplification lemma
- `#check expr` — type-checks an expression inline. Printed by the CLI and reported under `checks` in `--json`; a `#check` that does not elaborate or type-check **fails the file** (v0.15 — before that it was computed and discarded)
- `import "stdlib/Nat.sroof"` — imports a stdlib file; stdlib lives in `stdlib/` at repo root (Nat, Bool, Char, String, List, PolyList, Vec, Option, Either, Pair, Sigma, Dictionary, Relation, Regex, Effect)
- Operator overloading via `operator (x: T1) + (y: T2): T3 = body` syntax, registered in `GlobalEnv.operators`
- `stdlib/bundles/*.bundle` — lemma-bundle manifests (docs/lemma-bundles.md). Documentation-level convention only; not parsed by the tool

**Simp rule modifiers** (`tactic/SimpRewriteDb.scala`): lemma names passed to `simplify` support suffixes:
- `h__rev` — rewrite backwards (RHS → LHS)
- `h__p10` — set priority 10 (higher = tried first; default 0)
- `h__rev__p10` — both

## CI Pipeline

Five parallel GitHub Actions jobs (`.github/workflows/ci.yml`):
1. **kernel-soundness** — trusted-kernel soundness gate
2. **test** — `sbt test` + end-to-end checks on `nat.sroof`/`int.sroof` + Effect runtime extraction (`scripts/check_effect_runtime.sh`)
3. **benchmarks** — `scripts/benchmark.py`, 3 runs, median thresholds
4. **native** — compile + link + smoke-test native binary
5. **sbt-plugin** — compile `sbt-sroof/` (Scala 2.12)

## Common Pitfalls

- **De Bruijn index bugs**: When modifying tactics in `Builtins.scala`, carefully track `shiftFrom`/`shiftBelow`/`subst` calls. Multi-variable defspecs are especially tricky (see commit bf0d869).
- **Native modules**: Don't add source files to `*-native/` directories — they share sources from JVM counterparts.
- **Parser changes**: `syntax/Parser.scala` uses Parsley combinators. Changes there may require updating `Elaborator.scala` in tandem.
- **Kernel trust boundary**: Tactics (`Builtins.scala`, `TacticM`) are NOT trusted. Every proof term must pass `Kernel.verify`; any shortcut that skips this check breaks soundness. This applies identically to both frontends.

**Indexed families work (v0.8–v0.13); `stdlib/Vec.sroof` just does not use them.** `CtorDef.retIndices` is populated by `Elaborator.elabInductive` and read by `IndChecker`. A constructor may declare `case vnil: Vec(A)(Nat.zero)`, the index is enforced, an indexed family may be a parameter type, and both `cases` and `induction` refine the index per branch.

Everything is gated on `IndChecker.isIndexedFamily` — indices declared **and** stated on every constructor. `stdlib/Vec.sroof` returns a bare `Vec`, so it keeps a phantom index and the pre-v0.10 behaviour; that is how it is written, not what the tool can do. `examples/vec_indexed.sroof` is the indexed form. See `docs/indexed-families.md`.

**A family that declares indices uses a `p+q`-wide De Bruijn window in `argTpes`, phantom or not.** `Elaborator.elabInductive` puts `(params ++ indices)` in scope unconditionally, so substituting with a `p`-wide spine lands every parameter one slot per index off. Use `IndChecker.paddedSpine`. This was invisible until `def` bodies were checked.

**Parameterised inductives: three coordinate rules (fixed in v0.7).** Each was invisible because it is the *identity* on a monomorphic type — so a passing monomorphic suite proves nothing about them.
1. `Builtins.buildFixCase` must instantiate a constructor's `argTpes` at the scrutinee's type arguments before extending the branch context. Raw `argTpes` refer to type parameters via `Var(j..j+m-1)` (the progressive convention `IndChecker.instantiateArgType` defines), which are bound nowhere in a branch context.
2. Branch contexts and the motive are stated in **`goal.ctx`**, not in a context with the induction variable removed. The removed-variable form only agrees with `goal.ctx` when every entry a branch mentions is newer than the induction variable.
3. `Fix`'s body embeds the scrutinee's type *inside* its own binder, so that copy needs `shift(1, ·)`.

**Generic enums in the frontend.** Type parameters become leading `Type`-valued value parameters in core; call sites must carry explicit type arguments (core does no inference). `CoreTranslator.translateInductive` builds constructor field types by hand because it is the one place not using ordinary innermost-first scoping. dotc gives each enum case its own type parameters and a `PolyType` constructor — instantiate it at the enum's type parameters (`InductiveExtractor.valueParams`).

**`.sroof` polymorphic types: declare the type parameter first.** `def f(A: Type, xs: PolyList(A), ...)` keeps a constructor field's type and the signature both in the *applied* form. Writing the type parameter last forces a bare `PolyList` in the signature, which will not match.

**Parameterless defs are NOT `Fix`-wrapped.** A nullary `Fix` never reduces (it only unfolds when applied), so it would sit unevaluated wherever it was inlined. `CoreTranslator.assemble` emits the body directly and rejects nullary self-recursion, matching the legacy elaborator.

**Scala frontend: `ih` targets the constructor's LAST field.** `Builtins.buildFixCase` applies the recursion to `Var(0)`, the last constructor argument, so an induction hypothesis exists only when that field has the inductive's own type. Locate it by binder identity against `fieldBinders.last` — never by iterating the binder map, whose order is unspecified (this was a real bug, fixed in v0.4).

**Scala frontend: the semantic bridge is trusted.** `frontend/CoreTranslator.scala` and `plugin/dotc/TreeExtractor.scala` decide *what core proposition a Scala theorem is about*. The kernel cannot check that correspondence, so a bug there yields a valid proof of the wrong statement. Keep the accepted subset small, give every accepted construct exactly one core reading, and pin it with a golden test. Never add a catch-all that turns an unrecognised tree into an IR node.

**Scala frontend: no `Meta` in accepted translations.** The expected type is threaded top-down and used verbatim as a `Mat` return type; `CoreTranslatorSuite` asserts no `Meta` survives. Since v0.7 a type may mention type parameters, so it is **no longer closed** — the expected type is now shifted when passed under match-branch and `let` binders. Any further widening of the type language means auditing that threading again.

**The kernel is asked one question; check what else the caller is asserting.** `Kernel.verify` answers "does this term have this claimed type" — not "is the claim a type", and not anything about terms it was never shown. Three v0.28 defects were all this: the Scala frontend never checked a `def` body against its declared type (the `.sroof` path had done so since v0.14), never checked a theorem's statement was a proposition, and let an `Eval` exception escape `ModuleVerifier.verify` as a compiler crash. **`Bidirectional.inferUniverse` is not a well-formedness check for `Eq`** — it returns `Right(0)` for an applied `Eq` without inspecting the arguments, so it accepts exactly the malformed statements you would be trying to reject. Infer one side and check the other against it. The `.sroof` path had the same blind spot (v0.29): it rejected an ill-typed statement, but reported it as `Internal error … This is a bug in sroof`, blaming the tool for what the author wrote. **That check applies to `Eq` statements only**: a defspec may state a bare type to be inhabited, and a *phantom*-index family's applied form cannot be typed at all (`infer` on `Ind` folds over parameters only), so requiring it rejects files that check today.

**Equality goals use the 2-arg `Eq` form** (`Eq.mkPropType`). The 3-arg form cannot be typed by the existing checker: `Ind("Eq", ...)` is a built-in absent from `GlobalEnv`, so `inferUniverse` only special-cases the 1- and 2-arg shapes.

**Plugin phase placement**: `runsAfter = PostTyper.name`, `runsBefore = Pickler.name`, via the compiler's own constants (resolving to `posttyper`/`pickler` in 3.3.6). That window is chosen because a `PartialFunction` literal is still `Block(DefDef, Closure)` over a `Match` there — later phases turn it into an anonymous class and the induction-case extraction would break.
**The CLI writes to exactly two paths, and both destroyed user files.** `sroof agent`'s output path was `replaceAll("\\.sroof$", ".repaired.sroof")` — the identity on any other name, so it overwrote its input while printing that it had written elsewhere (v0.33). `sroof extract --output <the input>` wrote extracted Scala over the proof source and exited 0 (v0.34). Both are now guarded (`repairedPathFor`, `wouldOverwriteInput`); if a third write path is added it owes the same guard, and path comparison must be **canonicalised** — `./x` and `x` are the same file and a string compare says otherwise.

**A `case _ =>` in a tactic traversal is how `--fail-on-sorry` got walked past.** `Checker.countSorryTactic` and `collectLemmaRefsTactic` defaulted, and the three tactics that carry a proof — `obtain` and `specialize` (each continues into another tactic) and `calc` (a proof per step) — fell into it, so a `sorry` under any of them counted as zero: plain `OK`, no warning, `--fail-on-sorry` exit 0 (fixed v0.32 by enumerating every case, so a new tactic fails to compile instead). The count also drives `skipKernel`, so an uncounted `sorry` sends the placeholder to the kernel and surfaces as a type mismatch about a term the author never wrote.

**`simpSet` must only hold names that resolve, and its producer owes that.** `Builtins.checkLemmaNames` skips the unresolvable-name guard for the *default* set, on the premise that those names exist by construction. That was false for `@[simp] defspec`: the elaborator registered the name before the proof existed (fixed v0.30 — the name now rides in `ElabResult.simpDefspecs` and `Checker` registers it once the proof is produced and un-`sorry`-tainted, matching what `frontend.ModuleVerifier` already did). The `sorry` angle is the sharp one: `simpSet` is consulted *implicitly*, while taint is propagated from lemma names a proof writes down, so a tainted implicit lemma leaves no trace. Note **`SimpSetSuite`'s "simplify with no lemmas uses @[simp] defspec" does not test that** — its goal is closed by `trivial` alone, so it passes either way; v0.31 added three cases sharing a goal `trivial` cannot close, which do establish it (the feature works, and the `sorry` leak above turned out not to occur on the previous tree either: a `sorry`-proved lemma does not fire).

- **`induction` vs `cases`**: `induction` wraps the proof in `Fix` when any case requests an IH (binding count > ctor arity). `cases` always uses plain `Mat` with no IH. Keep this distinction when adding new case-analysis tactics.
**`sbt-sroof` is compiled by CI and never run.** Its `sroofExtract` invokes `sroof extract <file> --output <file>` and is wired into `Compile / sourceGenerators`, so when the CLI did not accept `--output` (until v0.25) every build that enabled the plugin failed. Anything the plugin depends on has to be pinned by a CLI-side test — `cli/ExitCodeSuite` covers the argument shapes it passes.

**Six entry points assemble the pipeline themselves, and they drift.** `processSource`, `processSourceWithWarnings`, `processSourceWithIncrementalStats` (the cached path, used by `sroof extract`), `processSourceWithChecks`, `processSourceJson`, and `processDeclaration` (the REPL) each stitch parse → elaborate → `checkAll` → `evalChecks` on their own. The same `#check` bug therefore shipped three times: files (fixed v0.15), the REPL (v0.22), and the cached path (v0.23, where it meant `sroof extract` emitted code from a file `sroof check` rejects). `cli/EntryPointAgreementSuite` asks all six the same question — add a phase to one and it will tell you about the other five.

**Extraction: the core has no node for a global reference.** The elaborator inlines a def's body at every use site, so `Extractor` has to match bodies back to their definitions (`ExtractCtx.defNames`, keyed on `Fix`-shaped bodies only — a non-recursive body can be as small as `Con("zero")`, and keying on that renames every `zero` in the program). Without it, every caller of `plus` emits a copy of `plus` as `{ def plus … ; plus }(x)(y)`, which does not parse.

**Extraction: an index is data, a proof is not.** The `enum` header drops the index *parameter*, which makes the constructor's index *argument* look erasable. It is not: it is exactly what a function taking the length is passed. Whatever `dataArgPositions` drops must be dropped identically by the `enum` case, by `Term.Con`, and by every `match` pattern — three places, one list.

**Extraction: hand-built `IndDef` fixtures encoded the wrong De Bruijn convention.** Inside `argTpes(j)` the constructor's own earlier arguments come first, then `(params ++ indices).reverse`. `ExtractorSuite`'s `Vec` fixture omitted the arguments and the extractor omitted them too, so the two agreed and the suite passed while `stdlib/Vec.sroof` extracted to `arg1: Any`. Check a fixture against a real elaborated file before trusting it.

- **`Eq` is special**: `Eq` is a built-in inductive handled specially in the kernel and in `tactic/Eq.scala`. Do not normalize the outer `Ind("Eq",...)` with NbE — the constructor name is lost and pattern matching breaks.
