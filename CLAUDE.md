# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is sproof?

A dependently-typed theorem prover (proof assistant) written in Scala 3. Uses a predicative Calculus of Inductive Constructions (CIC) with Scala-like brace syntax. The goal is making formal verification accessible to programmers familiar with Scala/Java/Rust/C++.

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

# Check a proof file
sbt "cli/run check examples/nat.sproof"

# Extract Scala 3 code from proofs
sbt "cli/run extract examples/nat.sproof --output Nat.scala"

# Build native binary (requires clang, lld, libunwind-dev)
sbt cliNative/nativeLink
```

## Module Dependency Graph

```
cli (entry point: sproof.Main)
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

Eight JVM modules + eight mirrored Scala Native modules. Native modules have no source of their own — they share sources from JVM counterparts via `unmanagedSourceDirectories` in build.sbt.

## Key Architecture Concepts

**De Bruijn indices**: All variable binding uses De Bruijn indices (not named variables). `Subst.scala` in core handles substitution and shifting. Off-by-one errors in index manipulation are the most common source of bugs, especially in `Builtins.scala` induction/cases tactics.

**Term ADT** (`core/Term.scala`): `Var`, `App`, `Lam`, `Pi`, `Let`, `Uni`, `Ind`, `Con`, `Mat`, `Fix`, `Meta`. This is the internal representation after elaboration.

**NbE (Normalization by Evaluation)** (`eval/`): Three files — `Eval.scala` (reduce to WHNF), `Quote.scala` (semantic values → terms), `Semantic.scala` (value domain with closures and neutral terms).

**Bidirectional type checking** (`checker/Bidirectional.scala`): Inference mode and checking mode. `IndChecker.scala` validates inductive type definitions.

**TacticM monad** (`tactic/TacticM.scala`): Pure functional proof state management via `Either[TacticError, ?]`. Tactics manipulate a goal stack with context.

**Elaboration pipeline**: `.sproof` file → `Parser.scala` (Parsley combinators) → `SurfaceAst` → `Elaborator.scala` → core `Term`s + `GlobalEnv`.

**Proof agent** (`cli/` — `TacticGen.scala`, `SearchLoop.scala`, `FileRepairer.scala`): BFS-style tactic search that auto-repairs `by sorry` placeholders. Generates candidates ordered by success probability (depth-0: trivial/assumption/simplify, depth-1: induction).

## sproof Language Syntax

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

Built-in tactics: `trivial`, `simplify [lemmas]`, `induction x { cases }`, `assumption x`, `apply f`, `cases x { cases }`, `have h : T = proof`, `calc { chain }`, `ring`, `sorry`.

## CI Pipeline

Three parallel GitHub Actions jobs:
1. **JVM tests** — `sbt test` + end-to-end checks on `nat.sproof` and `int.sproof`
2. **Scala Native** — compile + link + smoke-test native binary
3. **sbt plugin** — compile `sbt-sproof/` (Scala 2.12)

## Common Pitfalls

- **De Bruijn index bugs**: When modifying tactics in `Builtins.scala`, carefully track `shiftFrom`/`shiftBelow`/`subst` calls. Multi-variable defspecs are especially tricky (see commit bf0d869).
- **Native modules**: Don't add source files to `*-native/` directories — they share sources from JVM counterparts.
- **Parser changes**: `syntax/Parser.scala` uses Parsley combinators. Changes there may require updating `Elaborator.scala` in tandem.
