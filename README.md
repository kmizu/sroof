# sroof

**A Proof Assistant for Programmers**

sroof is a dependently-typed theorem prover written in Scala 3. It aims to make formal verification accessible to programmers who already know Scala, Java, Rust, or C++.

[![CI](https://github.com/kmizu/sroof/actions/workflows/ci.yml/badge.svg)](https://github.com/kmizu/sroof/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

---

## Why sroof?

Traditional proof assistants (Coq, Lean, Agda) haven't reached mainstream programmers — not just because dependent types are hard, but because **the syntax acts as an unnecessary barrier**.

```coq
(* Coq — readable without prior knowledge? *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.
```

```scala
// sroof — readable if you know Scala/Java/Rust
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

> **Where sroof is heading.** The `.sroof` language above is the mature path and
> is fully supported. Alongside it there is now a **Scala 3 frontend**: you write
> ordinary `.scala` files, and a compiler plugin proves annotated theorems during
> compilation. It currently supports a deliberately narrow subset — see
> [Verifying ordinary Scala 3](#verifying-ordinary-scala-3-initial-subset).

sroof's design principle: **keep only the essential complexity**.

- **Learning cost = type theory concepts only** — syntax adds no extra burden
- **Uniform brace `{ }` syntax** — familiar to anyone who knows Java, Rust, or Scala
- **Full English tactic names** — `trivial`, `induction`, `simplify` (no cryptic abbreviations)
- **Short aliases available** — `triv`, `simp`, `rw` (only self-evident abbreviations)
- **Helpful error messages** — point to the next step, not internal jargon

---

## Comparison

|                    | Coq        | Lean 4       | sroof                  |
|--------------------|------------|--------------|-------------------------|
| Implementation     | OCaml      | C++          | **Scala 3**             |
| Type theory        | CIC        | CIC          | **Predicative CIC**     |
| Syntax             | Math-first | Improved DSL | **Scala-like, braces**  |
| Extraction target  | OCaml/Haskell | Lean itself | **Scala 3 (default)**  |
| Native binary      | —          | —            | **Scala Native**        |
| Reflexivity tactic | `rfl`      | `rfl`        | **`trivial`**           |
| Intro tactic       | `intros`   | `intro`      | **`assume`**            |

---

## Quick Start

```bash
# Clone and build
git clone https://github.com/kmizu/sroof
cd sroof
sbt cli/run

# Check a proof file
sbt "cli/run check examples/nat.sroof"
```

### Output

```
OK: examples/nat.sroof — 1 inductive(s), 1 definition(s), 4 defspec(s)
```

JSON output schema is documented in [docs/json-schema.md](docs/json-schema.md).
Proof onboarding recipes: [docs/proof-cookbook.md](docs/proof-cookbook.md)
Effect boundary guidance: [docs/effects.md](docs/effects.md)

### Incremental Check Cache

Repeated checks in the same JVM process reuse parse/elaboration/proof results with staged invalidation.

- strategy document: [`INCREMENTAL_CHECKING.md`](INCREMENTAL_CHECKING.md)
- safe fallback: if cache keys mismatch, sroof re-checks from the affected stage

### Benchmark Suite

```bash
python3 scripts/benchmark.py --runs 3 --thresholds benchmarks/thresholds.json --output benchmarks/results.json
```

- uses multiple runs and median to reduce noise
- compares workload medians against CI thresholds
- writes a machine-readable report at `benchmarks/results.json`

### v0.9 Release Notes

- changelog: [`CHANGELOG.md`](CHANGELOG.md)
- release notes: [`RELEASE_NOTES_v0.8.md`](RELEASE_NOTES_v0.8.md)
- release checklist: [`RELEASE_CHECKLIST_v0.8.md`](RELEASE_CHECKLIST_v0.8.md)
- publishing setup: [`docs/publishing.md`](docs/publishing.md)
- previous releases: [`RELEASE_NOTES_v0.7.md`](RELEASE_NOTES_v0.7.md), [`RELEASE_NOTES_v0.6.md`](RELEASE_NOTES_v0.6.md), [`RELEASE_NOTES_v0.5.md`](RELEASE_NOTES_v0.5.md), [`RELEASE_NOTES_v0.4.md`](RELEASE_NOTES_v0.4.md)

### Migration Notes (v0.7 -> v0.8)

- **Nothing breaks.** All 590 tests pass unchanged.
- The parser accepts strictly more: a constructor's return type may carry index
  arguments, as in `case vnil: Vec(A)(Nat.zero)`. Indices are recorded but not
  yet read by the checker — see [`docs/indexed-families.md`](docs/indexed-families.md).

### Migration Notes (v0.6 -> v0.7)

- **Nothing breaks.** All 584 tests from v0.6 still pass.
- Generic enums are newly accepted, so the diagnostic that rejected them is gone.
- Induction over parameterised inductives works on the `.sroof` path too;
  declare the type parameter **first** so a constructor field's type and a
  definition's parameter type are both the applied form.

### Migration Notes (v0.5 -> v0.6)

- **Nothing breaks.** `have` is additive; every v0.5 program still verifies.

### Migration Notes (v0.4 -> v0.5)

- **Nothing breaks.** Every v0.4 program still compiles and verifies.
- The induction-hypothesis diagnostics are now shared between `ih` and `exactIh`,
  so their wording changed slightly. Check tooling that matches plugin output.

### Migration Notes (v0.3 -> v0.4)

- **Nothing breaks.** Every v0.3 program still compiles and verifies; the changes
  are all widenings of what the Scala frontend accepts.
- One diagnostic changed wording: `ih` on the wrong binder now says
  "last (recursive) field". Check any tooling that matches on plugin output.

### Migration Notes (v0.2 -> v0.3)

- **Nothing breaks.** The `.sroof` language, CLI, stdlib, examples, VS Code
  extension, sbt plugin, and native binary all behave exactly as in v0.2.
- The Scala 3 frontend is additive: if you do not enable the compiler plugin,
  your build is unaffected.
- The trust model gained a second, explicitly stated claim for the Scala path —
  see [`docs/trust-model.md`](docs/trust-model.md) before relying on it.
- Documentation corrections: the tactic reference previously listed `ring` and
  the alias `induct` (neither exists) and conflated `assumption` with `assume`;
  the native binary is `sroof-cli-native`, not `sroof-cli-native-out`.

### Migration Notes (v0.1 -> v0.2)

- Core CLI commands are unchanged.
- `check --json` remains the machine-readable integration path.
- `examples/vec.sroof` uses argument ordering in `concat` that is compatible with structural recursion checking.

---

## Language Guide

### Inductive Types

```scala
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

inductive List(A: Type) {
  case nil: List(A)
  case cons(head: A, tail: List(A)): List(A)
}

inductive Bool {
  case true:  Bool
  case false: Bool
}
```

### Function Definitions

```scala
// Block body
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// Expression body
def id(x: Nat): Nat = x
```

### Specification Definitions (`defspec`)

`defspec` expresses the Curry-Howard correspondence directly:
**proposition = type**, **proof = program**.

```
defspec name(params): proposition { proof }
```

Symmetry with `def`:

```scala
def     foo(n: Nat): Nat  =         { n }          // function: program for a type
defspec bar(n: Nat): P(n) { ... }        // spec: proof program for a proposition
```

If the proof program has the wrong type, it is rejected — just like a type error in regular code.

### Tactic Proofs

```scala
// Trivial: both sides reduce to the same term
defspec plus_zero_left(m: Nat): plus(Nat.zero, m) = m {
  by trivial
}

// Induction with induction hypothesis
defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

### Term Proofs (direct Curry-Howard terms)

```scala
defspec refl_intro(n: Nat): n = n {
  by induction n {
    case zero   => trivial
    case succ k => trivial
  }
}
```

---

## Tactic Reference

### Closing a goal

| Tactic          | Aliases        | Effect                                                     |
|-----------------|----------------|------------------------------------------------------------|
| `trivial`       | `triv`, `rfl`  | Close a goal whose two sides are definitionally equal      |
| `decide`        | —              | Close a decidable goal (currently the same as `trivial`)   |
| `assumption`    | —              | Close the goal using a hypothesis already in context       |
| `contradiction` | —              | Close any goal from a contradictory hypothesis             |
| `tauto`         | —              | Discharge a propositional tautology                        |
| `exact e`       | —              | Close the goal with the explicit proof term `e`            |
| `sorry`         | —              | Unsound placeholder for an incomplete proof (warns)        |
| `skip`          | —              | Do nothing                                                 |

### Rewriting and case analysis

| Tactic                              | Aliases           | Effect                                                       |
|-------------------------------------|-------------------|--------------------------------------------------------------|
| `simplify [f, g, ...]`              | `simp`            | Rewrite with the listed lemmas, then close. With no list, uses the `@[simp]` set |
| `rewrite [h]`                       | `rw [h]`          | Rewrite the goal with the given equations                    |
| `induction x { ... }`               | —                 | Split on constructors of `x`; recursive cases get an IH      |
| `induction x generalizing y z {...}`| —                 | As above, with the IH universally quantified over `y`, `z`   |
| `cases x { ... }`                   | —                 | Split on constructors without an induction hypothesis        |

### Structure and logic

| Tactic                        | Aliases            | Effect                                                  |
|-------------------------------|--------------------|---------------------------------------------------------|
| `assume x ...`                | `intro`, `intros`  | Introduce `∀`-bound variables into the context          |
| `apply f`                     | —                  | Reduce the goal via `f`'s codomain, leaving its domain  |
| `have h : T = { p }; rest`    | —                  | Introduce a local lemma, then continue with `rest`      |
| `calc { ... }`                | —                  | Chain equational reasoning steps                        |
| `split` / `constructor`       | —                  | Split a conjunction / apply the sole constructor        |
| `left` / `right`              | —                  | Choose the first / second constructor of a disjunction  |
| `use e`                       | `exists e`         | Provide a witness for an existential                    |
| `obtain [x y] from h`         | —                  | Destructure a hypothesis                                |
| `specialize h arg`            | —                  | Instantiate a universally quantified hypothesis         |
| `by_contra h`                 | —                  | Proof by contradiction: assume the negation as `h`      |

### Combinators

| Form                        | Effect                                             |
|-----------------------------|----------------------------------------------------|
| `{ t1; t2; t3 }`            | Run tactics in sequence                            |
| `try t`                     | Run `t`; succeed regardless                        |
| `first \| t1 \| t2`         | Run the first alternative that succeeds            |
| `repeat t`                  | Run `t` until it stops making progress             |
| `all_goals t`               | Run `t` against every remaining goal               |

**Simp rule modifiers**: a lemma name passed to `simplify` accepts suffixes —
`h__rev` rewrites backwards, `h__p10` raises its priority (higher goes first),
`h__rev__p10` does both.

**Tip for beginners**: Write full names first (`trivial`, `induction`, `simplify`). Switch to aliases only once you understand what they mean.

---

## Coq Syntax Comparison

| Concept              | Coq                     | sroof                             |
|----------------------|-------------------------|------------------------------------|
| Inductive type       | `Inductive Nat : Set :=` | `inductive Nat {`                 |
| Function definition  | `Fixpoint plus ...`      | `def plus ...`                    |
| Theorem              | `Theorem plus_zero ...`  | `defspec plus_zero ... {`|
| Begin proof          | `Proof.`                 | `{`                               |
| End proof            | `Qed.`                   | `}`                               |
| Reflexivity          | `reflexivity` / `rfl`    | `trivial`                         |
| Simplify             | `simpl` / `simp`         | `simplify` / `simp`               |
| Introduce hypothesis | `intros`                 | `assume`                          |
| Induction            | `induction n`            | `induction n {`                   |

---

## Scala 3 Extraction

```bash
sbt "cli/run extract examples/nat.sroof --output Nat.scala"
```

Proofs (propositions) are erased at runtime; only the computational content remains.

```scala
// sroof
def plus(n: Nat, m: Nat): Nat { ... }
defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n { ... }

// Generated Scala 3
def plus(n: Nat, m: Nat): Nat = ...
def plus_zero_right(n: Nat): Unit = ()   // proof erased
```

---

## Verifying ordinary Scala 3 (initial subset)

Instead of writing a `.sroof` file, you can write ordinary Scala and have the
sroof compiler plugin prove theorems about it during compilation:

```scala
import sroof.annotation.*
import sroof.lang.*

@proofModule
object NatProofs:

  enum Nat:
    case Zero
    case Succ(n: Nat)

  import Nat.*

  def plus(n: Nat, m: Nat): Nat =
    n match
      case Zero    => m
      case Succ(k) => Succ(plus(k, m))

  @theorem
  def plusZeroRight(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )
```

Scala's own parser and typer process this file; `Nat` and `plus` stay the real
program and are not regenerated. What the plugin adds is that `plusZeroRight` is
proved at compile time and re-checked by the same trusted kernel the `.sroof`
path uses. If the theorem stopped holding, the file would stop compiling.

**This is a subset, not general Scala verification.** Today it covers: enums —
**generic or not** — pure `def`s and theorems over them (curried and generic
parameter lists included), self-recursion accepted by the termination checker,
exhaustive matches, runs of immutable local `val`s, parameterless definitions,
equality goals, and the tactics `trivial`, `induction`, `inductionGeneralizing`,
`cases`, `ih`, `exactIh`, `have`, `simplify`, and `rewrite`. Everything else —
`var`, effects, exceptions, casts, closures, GADTs, mutual recursion, external
calls — is **rejected with a diagnostic**, not approximated.

Worked examples of elementary mathematics live in `examples-scala3/`:
[`Arithmetic.scala`](examples-scala3/src/main/scala/sroof/examples/scala3/Arithmetic.scala)
proves the Peano addition and multiplication laws, and
[`Lists.scala`](examples-scala3/src/main/scala/sroof/examples/scala3/Lists.scala)
proves the list laws over a generic list. Both are compiled with the plugin, so
they are checked on every build rather than merely illustrative.

Verification only happens when the plugin is enabled by the build. The
annotations alone do nothing:

```scala
Compile / scalacOptions += "-Xplugin:" + pluginClasspath   // see build.sbt
```

Full details, including the exact supported and unsupported subsets and the
translation rules, are in [docs/scala3-frontend.md](docs/scala3-frontend.md).
A working example lives in `examples-scala3/`.

---

## Architecture

```
sroof/
├── core/            # Term ADT, De Bruijn substitution, typing context
├── eval/            # Normalization by Evaluation (NbE)
├── checker/         # Bidirectional type checking
├── tactic/          # TacticM monad, built-in tactics
├── syntax/          # Parsley-based parser, surface AST, pretty-printer  (legacy .sroof path)
├── extract/         # Scala 3 code generation                            (legacy .sroof path)
├── kernel/          # Trusted kernel (<500 lines, auditable)
├── cli/             # REPL and file loader                               (legacy .sroof path)
├── scala-api/       # @proofModule / @theorem annotations and the sroof.lang DSL
├── scala-frontend/  # Resolved IR, Scala-to-core translation, proof runner, kernel gate
├── scala-plugin/    # The Scala 3 compiler plugin (compiler-version-specific)
├── examples-scala3/ # Real .scala sources compiled with the plugin enabled
└── scala-it/        # Integration tests that invoke dotc for real
```

## Trust Model

Soundness boundary and trusted computing base (TCB) are documented in [docs/trust-model.md](docs/trust-model.md).

Pipeline note:
- checker/tactic generates candidate proof terms
- final accept/reject decision is centralized in `kernel` validation

On the Scala 3 path the kernel decides logical validity exactly the same way, but
one extra thing is trusted: that the core model **is** the Scala program. That
Scala-to-core correspondence rests on the translation layer, so it is part of the
TCB for theorems stated about Scala code. See the trust-model document.

**Type theory**: Predicative CIC (Calculus of Inductive Constructions)
- Universe hierarchy: `Type`, `Type1`, `Type2`, ...
- Inductive types + fixpoints (recursive functions)
- Curry-Howard isomorphism (proof = program)

---

## Scala Native (native binary)

sroof compiles to a self-contained native binary via [Scala Native](https://scala-native.org/). No JVM required at runtime.

### Prerequisites

```bash
# Ubuntu / WSL2
sudo apt-get install clang lld libunwind-dev
```

### Build

```bash
# Compile all modules for native (requires clang)
sbt cliNative/nativeLink

# Run the native binary
./cli-native/target/scala-3.3.6/sroof-cli-native check examples/nat.sroof
```

### Performance

The native binary uses `releaseFast` + `LTO.thin` + `immix` GC by default. For maximum performance (slower to link):

```sbt
// in build.sbt, change releaseFast → releaseFull in nativeLinkSettings
```

### Checking native compilation (without linking)

```bash
# Compile all native modules (only requires Scala Native sbt plugin, no LLVM):
sbt cliNative/compile
```

---

## sbt Plugin

See [sbt-sroof](sbt-sroof/README.md) for integrating sroof into an sbt build.

```sbt
// project/plugins.sbt
addSbtPlugin("io.sroof" % "sbt-sroof" % "0.1.0")

// build.sbt
enablePlugins(SroofPlugin)
```

```bash
sbt sroofCheck    # Type-check all .sroof files
sbt sroofExtract  # Extract to Scala 3 source (runs before compile)
sbt sroofRepl     # Interactive REPL
```

## stdlib v1

Baseline stdlib modules for `Nat`, `List`, `Vec`, and `Bool` are available under [`stdlib/`](stdlib).

- Layout and naming conventions: [docs/stdlib.md](docs/stdlib.md)
- Usage examples: [`examples/stdlib/`](examples/stdlib)

---

## stdlib Bundles

Reusable lemma bundle manifests are available under `stdlib/bundles/`.

- Bundle documentation and compatibility policy: [docs/lemma-bundles.md](docs/lemma-bundles.md)
- Representative bundle-oriented example: [examples/bundles/nat_bundle_usage.sroof](examples/bundles/nat_bundle_usage.sroof)

---

## License

MIT
