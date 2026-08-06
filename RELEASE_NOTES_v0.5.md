# sroof v0.5 Release Notes

Release date: 2026-08-06

v0.3 established the Scala 3 frontend and v0.4 widened the Scala it parses. v0.5
is the first release to widen what it can **prove**, and to replace a batch of
documented-but-untested claims with tested ones.

## Generalized induction

Some goals cannot be proved by induction alone. When the goal's other parameters
change as the recursion proceeds, a hypothesis fixed at their original values
says nothing about the recursive call:

```scala
def alwaysZero(n: Nat, acc: Nat): Nat =
  n match
    case Zero    => Zero
    case Succ(k) => alwaysZero(k, Succ(acc))   // acc changes at every step

@theorem
def alwaysZeroIsZero(n: Nat, acc: Nat): Proof =
  prove(alwaysZero(n, acc) === Zero)(
    inductionGeneralizing(n, acc) {
      case Zero    => trivial
      case Succ(k) => exactIh(k)(Succ(acc))
    })
```

`inductionGeneralizing` quantifies the hypothesis over `acc`; `exactIh`
instantiates it at the value this branch actually recursed with. The suite pins
that this goal is provable **neither** by `trivial` nor by plain `induction`, so
the combinator is demonstrably doing work rather than decorating a proof that
would have gone through anyway.

The two are a pair. A quantified hypothesis has a `Pi` type, and `simplify`
cannot consume one — it looks for an equation. Inside `inductionGeneralizing`,
reach for `exactIh`; inside plain `induction`, `simplify(ih(k))` remains the
usual move.

`exactIh`'s arguments are expressions rather than plain names, because the
instantiations that matter are at *changed* values. They are resolved by name
against the proof context the tactic engine builds — the same way the engine
addresses that context internally — and only variables, constructor
applications, and calls to verified definitions are permitted there.

## Parameterless definitions

```scala
def two: Nat = Succ(Succ(Zero))

@theorem
def twoPlusZero: Proof = prove(plus(two, Zero) === two)(trivial)
```

This did not work before, and the way it failed is worth recording. Two separate
defects were stacked:

1. A reference to a parameterless definition arrives with **no enclosing
   `Apply`** to carry an argument list, so it fell through to "neither a binder
   nor a constructor of this proof module".
2. Once that was fixed, evaluation failed. Parameterless definitions were
   `Fix`-wrapped like any other, and a nullary `Fix` can never reduce — it only
   unfolds when applied, and there is nothing to apply it to — so it sat
   unevaluated wherever it was inlined. They now translate to their body
   directly, matching the legacy elaborator, and nullary self-recursion is
   rejected with a diagnostic rather than left as a dangling reference.

## Documented claims, now tested

A subset table nobody exercises is a table that can quietly stop being true —
which for a verification tool is worse than an honest omission. A new suite
compiles each of these for real: inferred local `val` types, `new Ctor(...)`,
enum cases written with an explicit `extends`, matching on the result of a call,
constructors with several non-recursive fields, all-wildcard patterns, mutually
referring enums, and parameterless definitions.

Seven passed on the first run. The eighth — parameterless definitions — did not,
which is the defect above.

## Generic enums: where the blocker actually is

Generic enums remain unsupported, and this release corrects the reason given for
it. Earlier documentation implied the work was frontend-side. It is not.

The core already represents parameterised inductives: `IndDef.params` holds the
type parameters, and a constructor's `argTpes` refer to them under a progressive
De Bruijn convention. What does not work is **induction** over them.
`Builtins.buildFixCase` extends a branch's context with the raw `argTpes`, which
still mention type parameters that are not bound in that context, so the indices
are wrong. For a monomorphic type there are no such references and the code is
correct by accident. `stdlib/PolyList.sroof` records the same limitation on the
`.sroof` side, offering only base-case proofs.

Supporting generic enums in the frontend alone would therefore deliver generic
declarations with no way to prove anything inductive about them — a sharp edge,
and worse than a clean rejection. The fix belongs in `Builtins`, benefits both
frontends, and should land before the frontend work. The rejection diagnostic now
says this, rather than "not supported in this milestone".

## Migration notes (from v0.4)

Nothing breaks. Every v0.4 program still compiles and verifies.

- All additions are widenings.
- The induction-hypothesis diagnostics are now generated in one place shared by
  `ih` and `exactIh`, so their wording changed slightly. Check any tooling that
  matches on plugin output.

## Known limitations

Unchanged from v0.4 apart from the additions above. Still rejected rather than
approximated: `var` and assignment, exceptions, I/O and calls outside the module,
casts, closures, partial application, generic enums and GADTs, classes and traits
as verified data, numeric and string primitives, macros and inline, pattern
guards, alternatives and nested patterns, mutual and non-structural recursion,
and theorem bodies not shaped as `prove(goal)(tactic)`.

`ih` and `exactIh` are still about a constructor's **last** field, and lemma
reuse is still limited to theorems verified earlier in the same module.

## Release artifacts

- Source release tag: `v0.5.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.5.0`)

The compiler plugin is still **not published**. Enable it from a local build via
`sroofPluginClasspath` (see `build.sbt`).

## Verification performed for this release

Every command below was run and passed:

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 571 passed, 0 failed |
| `sbt "cli/run check examples/nat.sroof"` | OK — 1 inductive, 1 definition, 4 defspec |
| `sbt "cli/run check examples/int.sroof"` | OK — 2 inductives, 8 definitions, 3 defspec |
| `sbt cliNative/compile` | success |
| `sbt cliNative/nativeLink` + native `check examples/nat.sroof` | success, OK |
| `cd sbt-sroof && sbt compile` | success |
| `cd vscode-sroof && npm ci && npm run compile` | success |
| `git diff --check` | clean |

The integration suite grew from 47 to 62 real `dotc` invocations; the total test
count from 556 to 571.
