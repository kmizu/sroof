# sroof v0.7 Release Notes

Release date: 2026-08-06

v0.5 identified the obstacle to generic types and deferred it. v0.6 tried, found
a second obstacle, and deferred again — recording exactly what it had found.
v0.7 goes through both.

**Induction over parameterised inductive types now works**, on both frontends.
On the Scala path that means generic enums; on the `.sroof` path it lifts a
limitation the standard library's polymorphic list has carried since it was
written.

## Generic enums

```scala
@proofModule
object Lists:

  enum Lst[A]:
    case Nil()
    case Cons(head: A, tail: Lst[A])

  import Lst.*

  def append[A](xs: Lst[A], ys: Lst[A]): Lst[A] =
    xs match
      case Nil()      => ys
      case Cons(h, t) => Cons(h, append(t, ys))

  @theorem
  def appendAssoc[A](xs: Lst[A], ys: Lst[A], zs: Lst[A]): Proof =
    prove(append(append(xs, ys), zs) === append(xs, append(ys, zs)))(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      })
```

Enums, definitions, and theorems may all take type parameters, and induction
works over the result.

## What was actually wrong

Three defects, stacked. Each is worth stating because each was invisible for the
same reason: **it is the identity transformation on a monomorphic type.**

**1. Constructor argument types were used raw.** `Builtins.buildFixCase` extended
a branch's context with the constructor's stored `argTpes`. Those follow the
convention `IndChecker.instantiateArgType` defines: within `argTpes(j)`,
`Var(0..j-1)` are the preceding fields and `Var(j..j+m-1)` are the inductive's
**type parameters**. A branch context binds no type parameters, so for a generic
enum those indices quietly pointed at `_rec` and `_n`. For a monomorphic enum
`m == 0` and there is nothing to point wrongly at, so the code was correct by
accident. The scrutinee's type arguments are now substituted in first.

**2. The branch context was built on the wrong context.** It removed the
induction variable, while the proof term the branches feed into is placed in the
goal's context. Those two agree only when every context entry a branch mentions
is *newer* than the induction variable. That holds for `defspec f(n, m)` with
induction on `n`, and for every shape in the test suite — and fails the moment a
type parameter is declared before the value being inducted on. Both are now
stated in the goal's context.

**3. `Fix`'s body needed a shift.** The `Fix` term embeds the scrutinee's type
both in its own type (stated outside its binder) and in its body (inside it). The
body's copy was not shifted. A monomorphic type is closed, so the shift is the
identity.

None of these could produce an unsound proof: the kernel re-checks every term,
so a wrong index is a rejected proof, not an accepted falsehood. What they
produced was "this cannot be proved", for reasons that read as unrelated type
errors.

## The `.sroof` path gains the same thing

`stdlib/PolyList.sroof` used to open with:

> NOTE: Structural-induction proofs over polymorphic inductives are not yet
> supported due to how type parameters are represented in constructor arg types.
> Only base-case (trivial) defspecs are provided here.

That note is gone, and the file now carries the inductive proofs it said were
impossible — `plist_append_nil_right` and `plist_copy_id`, both by induction with
the hypothesis.

One convention matters and is now documented in the file: **declare the type
parameter first**. Writing `def f(xs: PolyList, ..., A: Type)` forces the bare
`PolyList` in the signature while a constructor field carries the applied
`PolyList(A)`, and those do not match. With `def f(A: Type, xs: PolyList(A), ...)`
both are applied and agree. (This was the "second blocker" v0.6 reported: it is
a convention to follow, not a defect to fix.)

## Worked examples of elementary mathematics

Two new example files, both compiled with the plugin enabled — so they are
checked, not illustrative:

**`examples-scala3/Arithmetic.scala`** builds the Peano laws in the order a
textbook would: the two defining equations of `plus` (which hold by computation),
their mirrors `plus(n, Zero) === n` and `plus(n, Succ(m)) === Succ(plus(n, m))`
(which need induction, because the goal is stuck while `n` is a variable),
associativity, and then the multiplication laws.

**`examples-scala3/Lists.scala`** does the same over a generic list: the unit
laws for `append`, associativity, and that `length` distributes over `append` —
a statement mixing both enums, `Lst[A]` on the inside and `Nat` on the outside.

Each theorem is annotated with *why* it needs the tactic it uses, which is the
part that is hard to guess from a subset table.

## Migration notes (from v0.6)

Nothing breaks. Every v0.6 program still compiles and verifies; all 584 tests
from v0.6 still pass.

- Generic enums are newly *accepted*, so the diagnostic that used to reject them
  is gone. A test asserting that rejection was replaced.
- `IndChecker.instantiateCtorArgTpe` and `extractIndParams` became public so the
  tactic engine could reuse them rather than restate the convention.

## Known limitations

Generic enums are supported; GADTs and indexed families are not, and neither are
variance annotations or bounded type parameters. Otherwise unchanged from v0.6:
`var` and assignment, effects, exceptions, casts, closures, partial application,
mutual and non-structural recursion, nested patterns, and cross-module lemma
reuse remain rejected rather than approximated.

`ih` and `exactIh` are still about a constructor's **last** field.

## Release artifacts

- Source release tag: `v0.7.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.7.0`)

The compiler plugin is still **not published**. Enable it from a local build via
`sroofPluginClasspath` (see `build.sbt`).

## Verification performed for this release

Every command below was run and passed:

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 590 passed, 0 failed |
| `sbt "cli/run check examples/nat.sroof"` | OK |
| `sbt "cli/run check examples/int.sroof"` | OK |
| `sbt "cli/run check stdlib/PolyList.sroof"` | OK — 4 inductives, 6 definitions, 5 defspec |
| `sbt cliNative/compile` | success |
| `sbt cliNative/nativeLink` + native `check examples/nat.sroof` | success, OK |
| `cd sbt-sroof && sbt compile` | success |
| `cd vscode-sroof && npm ci && npm run compile` | success |
| `git diff --check` | clean |

The integration suite grew from 75 to 81 real `dotc` invocations; the total test
count from 584 to 590.
