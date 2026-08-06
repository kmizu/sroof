# sroof v0.3 Release Notes

Release date: 2026-08-06

## What changed

sroof used to be a proof assistant with Scala-*like* syntax. As of v0.3 it is a
**Scala 3 verification system with an independent proof kernel**. You write
ordinary `.scala` files; a standard Scala 3 compiler plugin proves the annotated
theorems during compilation and puts every proof through the same trusted kernel
the `.sroof` path has always used.

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

Scala's own parser and typer process this file. `Nat` and `plus` remain the real
program — they are not regenerated from proof terms. If `plusZeroRight` stopped
holding, the file would stop compiling.

## Why this direction

Familiar syntax solved the *reading* problem but left three structural ones: a
second language still needs its own IDE, build, and refactoring story; extraction
runs the wrong way, so the verified artifact and the shipped artifact are
different objects; and every language feature had to be re-invented for a
language nobody writes anything else in.

Embedding in Scala 3 inverts all three. The program is the Scala program, the
Scala compiler does the parsing and typing, and sroof contributes exactly one
thing: a proof obligation checked by an independent kernel.

## Highlights

- **New modules.** `scala-api` (annotations + DSL), `scala-frontend`
  (dotc-independent IR, translation, proof runner, kernel gate), `scala-plugin`
  (the compiler plugin), `examples-scala3`, `scala-it`.
- **Proofs are inert at runtime.** `Prop`, `Proof`, and `Tactic` are opaque
  aliases of `Unit`, and `prove` takes both arguments by name and discards them.
  No reflection, no runtime proof checking.
- **Fails closed.** Anything outside the supported subset is a positioned
  compiler error, never an approximated translation. A `@theorem` outside a
  `@proofModule` is an error too — an ignored annotation would let an unproved
  "theorem" compile clean.
- **Recognition is by symbol, never by name.** A user-defined `prove`,
  `trivial`, `simplify`, or `===` is ordinary Scala as far as sroof is concerned.
- **The kernel is unchanged.** Not one line, and no kernel test was weakened.

## Getting started

```bash
sbt scalaExamples/compile   # compiles real .scala with the plugin; a failed proof fails the build
sbt scalaExamples/test      # the verified module still runs as an ordinary Scala program
sbt scalaIt/test            # positive, negative, and symbol-identity tests over real dotc runs
```

Verification happens only when the build enables the plugin. The annotations on
their own do nothing:

```scala
Compile / scalacOptions += "-Xplugin:" + pluginClasspath   // see build.sbt
```

Full details are in [`docs/scala3-frontend.md`](docs/scala3-frontend.md).

## Trust model: read this if you rely on the guarantee

v0.3 introduces a distinction that did not previously exist, and it is stated
plainly in [`docs/trust-model.md`](docs/trust-model.md):

- **Core logical validity** — the generated proof term inhabits the claimed core
  proposition. Decided by the trusted kernel, exactly as before, on both paths.
- **Scala semantic correspondence** — the claim that the core proposition is
  about the Scala program you actually wrote. The kernel cannot check this: it
  sees core terms and has no way to know whether they model your source.

The second claim rests on the Scala-to-core translation, so that translation is
**inside the trusted computing base** for theorems stated about Scala code.
Describing the Scala frontend as wholly outside the TCB would be false, and we do
not.

The mitigation is to keep the bridge small enough to audit and to test the
correspondence directly: golden tests pinning the exact core term for `Nat` and
`plus`, a finite differential test comparing Scala `plus` against core
evaluation, negative tests ensuring unsupported Scala is rejected rather than
mistranslated, and an assertion that no accepted translation contains an
unresolved metavariable.

## Migration notes (from v0.2)

Nothing you already have breaks.

- The `.sroof` language, parser, elaborator, CLI (`check`, `agent`, `extract`,
  `repl`), stdlib, examples, VS Code extension, sbt plugin, and Scala Native
  binary all behave exactly as in v0.2.
- The Scala 3 frontend is additive. If you do not enable the compiler plugin,
  your build is unaffected.
- `sbt-sroof` is unchanged and is now documented as legacy `.sroof` integration.
  A future mode that injects `scala-api` and the compiler plugin is designed and
  recorded, but deliberately not implemented until the artifacts are published —
  a half-working packaging story would be worse than an honest note.
- Documentation corrections worth knowing about: the tactic reference previously
  listed `ring` and the alias `induct`, neither of which exists in the parser,
  and conflated `assumption` with `assume`. The native binary is
  `sroof-cli-native`, not `sroof-cli-native-out`.

## Known limitations

The Scala 3 frontend is an **initial subset**, not general Scala verification.

Supported inside a `@proofModule`: non-generic enums, `def`s with one parameter
list and explicit types over those enums, direct self-recursion accepted by the
termination checker, exhaustive matches, a single immutable local `val`, equality
goals, and the tactics `trivial`, `induction`, `ih`, and `simplify`.

Rejected with a diagnostic: `var` and assignment, exceptions, I/O and any call
outside the module, casts, closures and higher-order values, generic enums and
GADTs, classes and traits as verified data, numeric and string primitives,
macros and inline, pattern guards, alternatives, and nested patterns, mutual and
non-structural recursion, and theorem bodies not shaped as `prove(goal)(tactic)`.

Two restrictions are sroof-specific rather than obviously unsupported:

- `ih` requires a constructor with exactly one field of its own inductive type,
  because the tactic engine applies the recursion to the last constructor
  argument. `Succ(n: Nat)` qualifies; `Node(l: Tree, r: Tree)` does not.
- A pattern binder may not be named `ih`; that name is reserved for the generated
  induction hypothesis.

On the `.sroof` side, the v0.2 limitations still apply: structural termination
checking is conservative, tactic automation is intentionally minimal, and `sorry`
is available but unsound.

## Release artifacts

- Source release tag: `v0.3.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.3.0`)

The compiler plugin is **not yet published** to a repository. Until it is, enable
it from a local build via `sroofPluginClasspath` (see `build.sbt`).

## Verification performed for this release

Every command below was run and passed:

| Command | Result |
|---|---|
| `sbt kernel/test` | 14 passed |
| `sbt clean test` (all modules, from scratch) | 539 passed, 0 failed |
| `sbt "cli/run check examples/nat.sroof"` | OK — 1 inductive, 1 definition, 4 defspec |
| `sbt "cli/run check examples/int.sroof"` | OK — 2 inductives, 8 definitions, 3 defspec |
| `sbt cliNative/compile` | success |
| `sbt cliNative/nativeLink` + native `check examples/nat.sroof` | success, OK |
| `cd sbt-sroof && sbt compile` | success |
| `cd vscode-sroof && npm ci && npm run compile` | success |
| `git diff --check` | clean |
