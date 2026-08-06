# sroof v0.4 Release Notes

Release date: 2026-08-06

v0.3 established the Scala 3 frontend. v0.4 widens the Scala it accepts and
tightens what was already there. The architecture, the kernel, and the `.sroof`
path are unchanged.

## What you can write now that you could not before

### Curried parameter lists

```scala
def add(n: Nat)(m: Nat): Nat = plus(n, m)

@theorem
def plusSuccLeft(n: Nat)(m: Nat): Proof =
  prove(plus(Succ(n), m) === Succ(plus(n, m)))(trivial)
```

Lists are flattened, because core types are curried regardless: `f(a: A)(b: B)`
and `f(a: A, b: B)` produce the same `Pi(a, A, Pi(b, B, _))`. Call sites are
checked against the flattened arity, so a partial application like `add(n)` is
rejected rather than quietly accepted.

### Runs of local `val`s

```scala
def chained(n: Nat): Nat =
  val once: Nat  = plus(n, Zero)
  val twice: Nat = plus(once, once)
  twice
```

Previously a verified definition could open with exactly one binding. Now it can
open with several, each visible to the next.

### Recursive fields that follow other fields

```scala
enum Tagged:
  case Empty
  case Cons(tag: Tag, rest: Tagged)

@theorem
def sizeIdempotent(t: Tagged): Proof =
  prove(size(size(t)) === size(t))(
    induction(t) {
      case Empty         => trivial
      case Cons(_, rest) => simplify(ih(rest))
    })
```

An induction hypothesis is generated whenever a constructor's **last** field has
the inductive's own type. Previously only single-field constructors qualified,
which ruled out every list-like shape.

The restriction that remains is real and is enforced: the tactic engine applies
the recursion to the last argument, so for `Node(l: Tree, r: Tree)` only `ih(r)`
is meaningful. `ih(l)` is rejected with a message naming the field it can offer,
rather than silently answered with the hypothesis for `r`.

### Two more tactics

```scala
cases(n) {                    // constructor split, no hypothesis
  case Zero    => trivial
  case Succ(k) => trivial
}

rewrite(ih(k))                // directed rewrite, alongside simplify
```

`ih` inside `cases` is rejected, with a message pointing at `induction`.

## Fixed

One of these was a latent bug that the widening would have turned into a real
one, and it is worth stating plainly:

- **The induction hypothesis was located by taking the head of an unordered map**
  of pattern binders. With single-field constructors that was accidentally
  correct — there was only one candidate. Accepting multi-field constructors
  would have made it bind the hypothesis to an arbitrary field. It is now looked
  up by binder identity against the constructor's last field. This is exactly the
  class of bug the trust model warns about: it would have produced a valid proof
  of a proposition about the wrong thing, which the kernel cannot detect.
- `ih` on an unnamed (`_`) recursive field reported "no recursive field"; it now
  asks for the field to be bound to a name.
- The diagnostic for an unsupported block still claimed only a single `val` was
  allowed.

## Deliberately still deferred: generic enums

Generic enums remain the largest gap, and this release does not close it. The
reason is recorded in `docs/scala3-frontend.md` rather than left implicit:
supporting them means touching the trusted translation layer in several places at
once — type parameters in constructor field types, in definition signatures, and
in applications — and each one is a new opportunity to get a De Bruijn index
wrong inside the layer that the kernel cannot check for us.

v0.3's trust model commits to keeping that bridge small enough to audit. Adding
generics as one item among several in a mixed release would contradict that. They
should land as their own milestone, with golden tests per construct.

## Migration notes (from v0.3)

Nothing breaks. Every v0.3 program still compiles and verifies.

- The additions are all widenings: code that was accepted before is accepted now.
- One diagnostic message changed wording (`ih` on the wrong binder now says
  "last (recursive) field"). If you match on plugin output in tooling, check it.

## Known limitations

Unchanged from v0.3 except where noted above. The Scala frontend still rejects,
rather than approximates: `var` and assignment, exceptions, I/O and calls outside
the module, casts, closures, partial application, generic enums and GADTs,
classes and traits as verified data, numeric and string primitives, macros and
inline, pattern guards, alternatives and nested patterns, mutual and
non-structural recursion, and theorem bodies not shaped as `prove(goal)(tactic)`.

Lemma reuse is still limited to theorems verified earlier in the same module.

## Release artifacts

- Source release tag: `v0.4.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.4.0`)

The compiler plugin is still **not published**. Enable it from a local build via
`sroofPluginClasspath` (see `build.sbt`).

## Verification performed for this release

Every command below was run and passed:

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 556 passed, 0 failed |
| `sbt "cli/run check examples/nat.sroof"` | OK — 1 inductive, 1 definition, 4 defspec |
| `sbt "cli/run check examples/int.sroof"` | OK — 2 inductives, 8 definitions, 3 defspec |
| `sbt cliNative/compile` | success |
| `sbt cliNative/nativeLink` + native `check examples/nat.sroof` | success, OK |
| `cd sbt-sroof && sbt compile` | success |
| `cd vscode-sroof && npm ci && npm run compile` | success |
| `git diff --check` | clean |

The integration suite grew from 32 to 47 real `dotc` invocations; the total test
count went from 539 to 556.
