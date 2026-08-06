# sroof v0.6 Release Notes

Release date: 2026-08-06

A smaller release than v0.5, and a deliberately shaped one: it adds the tactic
that lets proofs be written in steps, converts another batch of untested claims
into tested ones, and reports a finding that changes the plan for generic enums.

## `have`: proofs in steps

Until now a branch had to be discharged by a single tactic. `have` proves an
intermediate equation and brings it into scope:

```scala
@theorem
def plusZeroRight(n: Nat): Proof =
  prove(plus(n, Zero) === n)(
    induction(n) {
      case Zero => trivial
      case Succ(k) =>
        have(plus(k, Zero) === k)(simplify(ih(k))) { step =>
          simplify(step)
        }
    })
```

The claim is proved as a goal in its own right and its proof term is bound by a
`Let`, mirroring the `.sroof` path's `have`. It is therefore not an assumption
mechanism: a claim that does not hold fails the theorem, which the suite pins.

The hypothesis is bound by the continuation's parameter, and its *name* is what
carries: the tactic engine puts the proved claim into the proof context under
that name and resolves citations there. Naming it `ih` is rejected, since that
name is reserved for the generated induction hypothesis.

`have` works inside an induction branch, where the interesting claims mention the
branch's binders, as well as at the top level of a proof.

## Documented claims, now tested

v0.5 established the habit of compiling every claim the subset table makes. Two
more suites do that here, and one of them covers a genuine silent-failure risk:

**Branch reordering.** `Term.Mat` matches branches to constructors **by
position**, and the frontend normalises the source order into constructor order.
If that normalisation were wrong, the result would not be a failure — it would be
a kernel-accepted proof about the wrong branches. Out-of-order `match` and
`induction` branches are now pinned by tests.

Also pinned: two `@proofModule` objects in one file (and a failure in the second
still failing the compilation), enums with more than two cases, transitive
inlining across a chain of definitions, `simplify` citing several verified
theorems at once, and deeply nested constructor expressions.

All eight passed on the first run. That is a less exciting result than v0.5,
where the same exercise found two real defects, and it is worth saying so
plainly rather than implying the tests were harder won than they were.

## Generic enums: a second blocker, found by trying

v0.5 identified `Builtins.buildFixCase` as the obstacle to induction over
parameterised inductives — it extends a branch context with raw constructor
argument types that still mention unbound type parameters. That is correct, and
this release attempted the fix.

Running an inductive proof over `PolyList` then produced:

```
expected: PolyList
actual:   (PolyList #2)
```

which is a different problem. `stdlib/PolyList.sroof` writes the **bare**
`PolyList` in its definition signatures, while a constructor field carries the
**applied** `PolyList(A)`. Instantiating the argument types correctly does not
reconcile those two spellings of the same type; that needs a decision about how
polymorphic types are modelled, not a De Bruijn correction.

So the work is ordered:

1. settle the bare-vs-applied convention for parameterised inductives;
2. instantiate `argTpes` in `Builtins.buildFixCase`;
3. add generic enums to the Scala frontend.

Steps 1 and 2 are changes to shared code with 584 passing tests behind them, and
they affect the `.sroof` path as much as the Scala one. They belong in their own
milestone. Shipping a half-finished attempt in this release, or widening the
frontend on top of a broken foundation, would contradict what the trust model
commits to — so neither was done.

## Migration notes (from v0.5)

Nothing breaks. Every v0.5 program still compiles and verifies; `have` is
additive.

## Known limitations

Unchanged from v0.5 apart from the addition of `have`. Generic enums, GADTs,
nested patterns, mutual recursion, effects, and cross-module lemma reuse remain
unsupported, and are still rejected with a diagnostic rather than approximated.

## Release artifacts

- Source release tag: `v0.6.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.6.0`)

The compiler plugin is still **not published**. Enable it from a local build via
`sroofPluginClasspath` (see `build.sbt`).

## Verification performed for this release

Every command below was run and passed:

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 584 passed, 0 failed |
| `sbt "cli/run check examples/nat.sroof"` | OK — 1 inductive, 1 definition, 4 defspec |
| `sbt "cli/run check examples/int.sroof"` | OK — 2 inductives, 8 definitions, 3 defspec |
| `sbt cliNative/compile` | success |
| `sbt cliNative/nativeLink` + native `check examples/nat.sroof` | success, OK |
| `cd sbt-sroof && sbt compile` | success |
| `cd vscode-sroof && npm ci && npm run compile` | success |
| `git diff --check` | clean |

The integration suite grew from 62 to 75 real `dotc` invocations; the total test
count from 571 to 584.
