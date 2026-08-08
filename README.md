# sroof

**A Proof Assistant for Programmers**

sroof is a dependently-typed theorem prover written in Scala 3. It aims to make formal verification accessible to programmers who already know Scala, Java, Rust, or C++.

[![CI](https://github.com/kmizu/sroof/actions/workflows/ci.yml/badge.svg)](https://github.com/kmizu/sroof/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

---

## What sroof is

**A Scala 3 verification system with an independent proof kernel.** You write
ordinary `.scala` files; a standard Scala 3 compiler plugin proves the annotated
theorems during compilation, and every proof is re-checked by a small trusted
kernel.

```scala
import sroof.annotation.*
import sroof.lang.*

@proofModule
object Arithmetic:

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

Scala's own parser and typer process this file. `Nat` and `plus` are the real
program — nothing is generated from proof terms, and the proofs erase to inert
values at runtime. What the plugin adds is that `plusZeroRight` is proved at
compile time. **If the theorem stopped holding, the file would stop compiling.**

Worked examples of elementary mathematics live in `examples-scala3/`:
[`Arithmetic.scala`](examples-scala3/src/main/scala/sroof/examples/scala3/Arithmetic.scala)
proves the Peano addition and multiplication laws;
[`Lists.scala`](examples-scala3/src/main/scala/sroof/examples/scala3/Lists.scala)
proves the list laws over a generic list. Both are compiled with the plugin, so
they are checked on every build.

### Why this rather than a language of its own

sroof began as a proof assistant with Scala-*like* syntax, on the premise that
syntax is what keeps proof assistants away from working programmers. That solved
the reading problem and left three others: a second language still needs its own
IDE, build, and refactoring story; extraction runs the wrong way, so the verified
artifact and the shipped artifact are different objects; and every language
feature has to be re-invented for a language nobody writes anything else in.

Embedding in Scala 3 inverts all three. The program *is* the Scala program, the
Scala compiler does the parsing and typing, and sroof contributes exactly one
thing: a proof obligation checked by an independent kernel.

**This is a subset, not general Scala verification.** See
[docs/scala3-frontend.md](docs/scala3-frontend.md) for exactly what is supported
and what is rejected — and it *is* rejected, with a diagnostic, rather than
approximated.

### The `.sroof` language

The original brace-syntax language is **still fully supported and not
deprecated**. It has the mature toolchain: a CLI, a standard library, extraction
to Scala 3, a native binary, and a VS Code extension. Several features reach it
first, since both paths share one core and one kernel.

```scala
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

Its guide is the [Language Guide](#language-guide) below.

---

## Comparison

|                    | Coq        | Lean 4       | sroof                  |
|--------------------|------------|--------------|-------------------------|
| Implementation     | OCaml      | C++          | **Scala 3**             |
| Type theory        | CIC        | CIC          | **Predicative CIC**     |
| You write proofs in | a bespoke language | a bespoke language | **ordinary Scala 3**, or the `.sroof` language |
| Verified at        | its own toolchain | its own toolchain | **`scalac`, as part of your build** |
| Extraction target  | OCaml/Haskell | Lean itself | **Scala 3** (`.sroof` path) |
| Native binary      | —          | —            | **Scala Native**        |

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

### Releases

- changelog: [`CHANGELOG.md`](CHANGELOG.md) — every release, in one place
- published releases: <https://github.com/kmizu/sroof/releases>
- publishing setup: [`docs/publishing.md`](docs/publishing.md)

### Migration Notes (v0.13 -> v0.14)

- **`def` bodies are now type-checked.** A definition whose body does not match its
  declared type is rejected. This was previously accepted, so a file that checked
  before may now fail — correctly. Five such definitions were found in this
  repository's own stdlib and examples.
- **Breaking:** `poly_length`, `poly_append`, `poly_reverse` and both `concat`s now
  take the type parameter **first**, e.g. `poly_length(A, xs)` and
  `concat(A, n, m, xs, ys)`. The previous signatures did not type-check.
- Evaluator failures are diagnostics rather than stack traces. If you caught
  `RuntimeException` from the API, you now get a `Left` instead.
- A dependently-typed definition's return index is verified, so
  `def vapp(...): Vec(A)(plus(n, m))` is a checked claim. See
  [`examples/vec_indexed.sroof`](examples/vec_indexed.sroof).

### Migration Notes (v0.12 -> v0.13)

- **Nothing breaks.** All 611 pre-existing tests pass unchanged; 616 in total.
- `induction` over an indexed family now carries a working induction hypothesis,
  stated at the recursive argument's index. See
  [`examples/vec_indexed.sroof`](examples/vec_indexed.sroof).
- It applies when the scrutinee's index is a plain context variable, the index
  type is closed, and there is one index. Everything else takes the previous path.
- Known limitation, pre-existing and now the binding one: a `def` body is not
  type-checked, so a dependently-typed definition's return index is not verified.
  See [`docs/indexed-families.md`](docs/indexed-families.md).

### Migration Notes (v0.11 -> v0.12)

- **Nothing breaks.** All 605 pre-existing tests pass unchanged; 611 in total.
- `cases` and `induction`-without-an-IH over an indexed family now refine the
  index per branch, so proofs about an arbitrary `Vec(A)(n)` are possible. See
  [`examples/vec_indexed.sroof`](examples/vec_indexed.sroof).
- An indexed family may now be used as a parameter type: `def f(A: Type, n: Nat,
  v: Vec(A)(n))`. This previously failed with `Expected function type, got Type`.
- Both changes are gated on the family stating an index on every constructor.
  A phantom-index declaration such as `stdlib/Vec.sroof` is untouched.
- Still unsupported: induction with an induction hypothesis over an indexed
  family. See [`docs/indexed-families.md`](docs/indexed-families.md).

### Migration Notes (v0.10 -> v0.11)

- **Nothing breaks.** 605 tests, no behaviour change to what is accepted or
  rejected.
- Failed proofs print correct hypothesis types. A dependent hypothesis used to
  render against a scope that included itself, so `v : Vec A n` showed as
  `Vec n v`. If you have tooling that parses `(hyp ...)` lines, it was reading
  shifted names.
- `checker.IndChecker` is documented as being inside the TCB — a correction to a
  comment, not a change in what is trusted. See
  [`docs/trust-model.md`](docs/trust-model.md).

### Migration Notes (v0.9 -> v0.10)

- **Nothing breaks.** All 590 pre-existing tests pass unchanged; 604 in total.
- **A soundness fix, so some files that checked before will now be rejected —
  correctly.** If a constructor declares its return index, as in
  `case vnil: Vec(A)(Nat.zero)`, that index is now enforced. Until v0.9 the
  checker took the index from the *expected* type, so `Vec.vnil` was accepted
  wherever a length-one vector was required.
- **Only families that state an index on every constructor are affected.** A
  declaration returning a bare `Vec` — which is every declaration written before
  v0.8, `stdlib/Vec.sroof` included — keeps its phantom index and its previous
  behaviour.
- Induction over an indexed family is still not supported; proofs about concrete
  vectors work. See [`docs/indexed-families.md`](docs/indexed-families.md) and
  [`examples/vec_indexed.sroof`](examples/vec_indexed.sroof).

### Migration Notes (v0.7 -> v0.8)

- **Nothing breaks.** All 590 tests pass unchanged.
- The parser accepts strictly more: a constructor's return type may carry index
  arguments, as in `case vnil: Vec(A)(Nat.zero)`. As of v0.8 those indices were
  recorded but not read by the checker; v0.10 made the checker enforce them.

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

## Language Guide (the `.sroof` language)

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

## Tactic Reference (the `.sroof` language)

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

## Supported Scala subset

See [docs/scala3-frontend.md](docs/scala3-frontend.md) for the exact supported
and unsupported subsets, the translation rules, and the trust boundary.

Enabling verification is a build decision — the annotations alone do nothing:

```scala
Compile / scalacOptions += "-Xplugin:" + pluginClasspath   // see build.sbt
```

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
