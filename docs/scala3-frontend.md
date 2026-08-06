# The Scala 3 frontend

sroof is becoming **a Scala 3 verification system with an independent proof
kernel, rather than a separate Scala-like programming language**. This document
describes the new primary path: ordinary `.scala` sources, verified during
compilation by a standard Scala 3 compiler plugin.

The legacy `.sroof` language, its parser, CLI, extractor, and examples all still
work and are unchanged. See [Migration](#migration-from-sroof) for how the two
relate.

---

## 1. Why abandon a separate Scala-like syntax

sroof's original premise was that syntax is what keeps proof assistants away
from mainstream programmers, so it offered a Scala-shaped language. That solved
the *reading* problem but left three structural ones:

- **A second language is still a second language.** A `.sroof` file cannot be
  compiled, tested, refactored, or reviewed with the tools a Scala team already
  has. Familiar syntax does not buy IDE support, build integration, or library
  reuse.
- **Extraction runs the wrong way.** Generating Scala *from* proofs means the
  verified artifact and the shipped artifact are different objects, and the
  correspondence between them is asserted rather than checked.
- **Every language feature had to be re-invented.** Parser, elaborator, type
  inference, and error messages all had to be built and maintained for a
  language nobody writes anything else in.

Embedding in Scala 3 inverts all three. The program is the Scala program; the
Scala compiler does the parsing, typing, and IDE work; and sroof adds exactly
one thing — a proof obligation checked by an independent kernel.

## 2. Architecture

```text
.scala source
    ↓  (Scala 3 parser and typer — unmodified)
typed trees
    ↓  scala-plugin: symbol-resolved extraction
resolved frontend IR (no dotc types)
    ↓  scala-frontend: translation
core Terms / IndDef / DefEntry / GlobalEnv
    ↓  existing tactics (untrusted generators)
candidate proof term
    ↓  Kernel.verify  ← the sole proof-validity gate
ordinary Scala compilation continues
```

### Modules

| Module | Depends on | Responsibility |
|---|---|---|
| `scala-api` | nothing but the Scala library | `sroof.annotation` markers and the `sroof.lang` DSL. Compiled into user code. |
| `scala-frontend` | `kernel` | The resolved IR, translation into core terms, the proof runner, and the kernel call. **Must not import `dotty.tools.dotc`.** |
| `scala-plugin` | `scala-frontend`, `scala3-compiler` (provided) | The `StandardPlugin`, its phase, and all dotc tree/symbol handling. Compiler-version-specific. |
| `examples-scala3` | `scala-api` | Real sources compiled with the plugin enabled; a failed proof fails this build. |
| `scala-it` | `scala-frontend` (test) | Integration tests that invoke `dotc` for real. |

The boundary that matters is `scala-frontend` ⊥ `dotc`. All compiler-specific
code lives in `sroof.plugin.dotc`, so porting to a future Scala version means
rewriting extraction only — not translation, proof running, or the kernel.

None of these are mirrored into the Scala Native build: the plugin links against
the JVM-only compiler. `nativeRoot` is untouched.

## 3. Developer-facing syntax

```scala
package sroof.examples.scala3

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

This is the file in `examples-scala3/`. It is ordinary Scala 3: it type-checks,
compiles, and runs without the plugin — it simply proves nothing in that case.

### Annotation and DSL reference

| Name | Meaning |
|---|---|
| `@proofModule` | Marks an `object` whose entire contents are verified code. |
| `@theorem` | Marks a method to prove. Must be in a `@proofModule`, return exactly `Proof`, and have the body `prove(goal)(tactic)`. |
| `@simp` | Adds a theorem to the default simplification set — only after the kernel accepts it. |
| `a === b` | The equality proposition. Both sides must be verified computations at a supported enum type. |
| `prove(goal)(tactic)` | States a goal and its proof script. Both arguments are by-name and never evaluated. |
| `trivial` | Closes a goal whose sides are definitionally equal. |
| `induction(x) { case ... }` | Structural induction on a theorem parameter. |
| `inductionGeneralizing(x, y, ...) { case ... }` | Induction whose hypothesis is universally quantified over the other named parameters. |
| `cases(x) { case ... }` | Constructor split with **no** induction hypothesis; `ih` is unavailable inside. |
| `ih(k)` | The induction hypothesis for the recursive field binder `k`. |
| `exactIh(k)(at...)` | Close the goal with that hypothesis, instantiated at the given values. The counterpart to `inductionGeneralizing`. |
| `have(claim)(proof) { h => ... }` | Prove an intermediate equation, bind it as `h`, and continue with it in scope. |
| `simplify(lemmas*)` | Rewrites with the given lemmas, then closes the goal. With no arguments, uses the `@simp` set. |
| `rewrite(equations*)` | Applies the given equations as directed rewrites. |

`Prop`, `Proof`, and `Tactic` are opaque type aliases of `Unit`. Proof code
therefore erases to inert values: nothing is executed, no reflection is
involved, and there is no runtime proof checking.

## 4. Supported subset

Inside a `@proofModule`, this milestone supports:

**Declarations**
- `enum`s, **generic or not**, whose case fields have supported types;
- `def`s with explicitly typed parameters and result, in one or more
  (curried) parameter lists, optionally with type parameters;
- `@theorem def`s returning exactly `sroof.lang.Proof`, likewise curried or
  generic;
- `@simp` on a theorem.

**Types**
- enums declared in the same `@proofModule`, applied to their type arguments;
- type parameters of the enclosing enum, definition, or theorem.

Nothing else: a primitive such as `Int`, or a type parameter that is not in
scope, is still an error.

**Expressions**
- parameter and pattern-binder references;
- calls to definitions of the same module, including direct self-recursion;
  curried calls are flattened, and partial application is rejected;
- enum constructor applications (`Succ(x)`, `Zero`, and `new Succ(x)`);
- exhaustive `match` over a supported enum, one branch per constructor;
- a run of immutable local `val` bindings, each visible to the next;
- transparent wrappers (`Typed`, `Inlined` with no bindings, empty `Block`).

**Proof DSL**
- equality goals built with sroof's `===`;
- `prove`, `trivial`, `induction`, `inductionGeneralizing`, `cases`, `ih`,
  `exactIh`, `have`, `simplify`, `rewrite`;
- `simplify`/`rewrite` citing a `@theorem` verified **earlier in the same
  module**, and bare `simplify()` drawing on the `@simp` set.

### Generalized induction

When the goal's other parameters change as the recursion proceeds, a hypothesis
fixed at their original values says nothing about the recursive call.
`inductionGeneralizing` quantifies the hypothesis over them, and `exactIh`
instantiates it:

```scala
@theorem
def alwaysZeroIsZero(n: Nat, acc: Nat): Proof =
  prove(alwaysZero(n, acc) === Zero)(
    inductionGeneralizing(n, acc) {
      case Zero    => trivial
      case Succ(k) => exactIh(k)(Succ(acc))
    })
```

The two go together. A quantified hypothesis has a `Pi` type, which `simplify`
cannot consume — it looks for an equation. Inside `inductionGeneralizing`, reach
for `exactIh`; inside plain `induction`, `simplify(ih(k))` is the usual move.

`exactIh`'s arguments are expressions, not just names, because the interesting
instantiations are at changed values. They are resolved **by name** against the
proof context the tactic engine builds, since that is how the engine addresses
that context itself; only variables, constructor applications, and calls to
verified definitions are allowed there.

### Generic enums

An `enum` may take type parameters, and definitions and theorems over it may too:

```scala
enum Lst[A]:
  case Nil()
  case Cons(head: A, tail: Lst[A])

def append[A](xs: Lst[A], ys: Lst[A]): Lst[A] = ...

@theorem
def appendAssoc[A](xs: Lst[A], ys: Lst[A], zs: Lst[A]): Proof =
  prove(append(append(xs, ys), zs) === append(xs, append(ys, zs)))(
    induction(xs) {
      case Nil()      => trivial
      case Cons(h, t) => simplify(ih(t))
    })
```

Three things make this work, and each is a place where the coordinates matter:

- **Type parameters become value parameters.** Core has no separate namespace for
  types, so `def f[A](x: Lst[A])` becomes `Pi(A, Type, Pi(x, Lst A, ...))`. They
  are quantified ahead of the value parameters, and a call site must pass them —
  which is why `ResolvedExpr.Call` carries explicit `typeArgs` recovered from the
  typed tree, rather than relying on Scala's inference having happened.
- **Constructor field types use a different De Bruijn convention.** In
  `IndDef.ctors`, `argTpes(j)` refers to the preceding fields as `Var(0..j-1)`
  and to the *type parameters* as `Var(j..j+m-1)`, with `Var(j)` the **last**
  parameter. This is the one place in the frontend that is not ordinary
  innermost-first scoping, and `CoreTranslator.translateInductive` builds it by
  hand for that reason.
- **dotc gives each case its own type parameters.** `case Cons[A](...)` has an
  `A` distinct from `enum Lst[A]`'s, and a generic case's constructor is a
  `PolyType`. The extractor instantiates that `PolyType` at the enum's own type
  parameters, which both resolves the field types and lines the case's parameters
  up with the enum's positionally.

`examples-scala3/Lists.scala` proves the usual list laws this way.

## 5. Explicitly unsupported

Rejected with a targeted diagnostic rather than approximated:

`var`, assignment, mutable fields · exceptions, `throw`/`try` · I/O, `println`,
any call outside the module · `Future`, threads · casts, `asInstanceOf` ·
implicit/given search in verified computation · closures, higher-order values,
and partial application · general, non-structural, or mutual recursion · GADTs
and indexed families · variance annotations and bounded type parameters ·
classes, traits, case classes, opaque types as verified data · numeric and string
primitives · macros, inline, quotes, splices · pattern guards, pattern
alternatives, nested patterns, `x @ pattern` · theorem bodies not shaped as
`prove(goal)(tactic)` · tactics other than the ones listed above.

Two restrictions are worth calling out because they are sroof-specific rather
than obviously unsupported:

- **`ih` is about the constructor's *last* field.** `Builtins.buildFixCase`
  applies the recursion to `Var(0)`, which is the last constructor argument, so
  the hypothesis exists exactly when that field has the inductive's own type.
  `Succ(n: Nat)` and `Cons(tag: Tag, rest: Tagged)` both qualify. For
  `Node(l: Tree, r: Tree)` only `ih(r)` would be meaningful, and `ih(l)` is
  rejected rather than silently answered with the hypothesis for `r`.
  The recursive field must also be bound to a name — `ih` cannot refer to a `_`.
- **A pattern binder may not be named `ih`.** The tactic engine binds the
  generated hypothesis under that exact name, so a user binder with the same name
  is rejected rather than allowed to shadow it.

Being legal Scala does not make code legal verified sroof code. Everything a
`@proofModule` declares is treated as verified code, so an unsupported member
fails the compilation instead of being silently skipped.

## 6. Compiler plugin

`sroof.plugin.SroofPlugin` is a `StandardPlugin` contributing one `PluginPhase`,
`sroofVerify`.

**Placement.** `runsAfter = PostTyper.name`, `runsBefore = Pickler.name`,
referenced through the compiler's own constants rather than string literals so a
rename cannot silently detach the phase. In Scala 3.3.6 the resolved names are
`posttyper` and `pickler`, and the surrounding order is
`typer → posttyper → … → pickler → inlining → …`. That window gives the phase:

- resolved symbols and inferred types on every tree;
- the user's original source positions;
- enum cases, method bodies, applications, and matches still in recognisable
  form — notably, a `PartialFunction` literal is still
  `Block(DefDef($anonfun), Closure)` over a `Match`, rather than the anonymous
  class it becomes later;
- execution before TASTy is written, so a rejected proof fails compilation rather
  than being pickled first.

The phase inspects and reports. It rewrites no trees.

**Symbol identity.** Every DSL operation, annotation, constructor, and binder is
recognised by comparing resolved `Symbol`s (`sroof.plugin.dotc.DslSymbols`). A
user-defined `prove`, `trivial`, `simplify`, or `===` is ordinary Scala as far as
sroof is concerned; `SymbolIdentitySuite` pins this behaviour.

**Version coupling.** `scala-plugin` depends on `scala3-compiler` at the exact
build version. Direct dotc usage is confined to the `sroof.plugin.dotc` package
so a future port does not touch the frontend or kernel.

**Lifecycle.** The plugin has no static mutable state. Resolved DSL symbols are
cached per compiler run and recomputed when the run changes, so nothing leaks
between compilations sharing a JVM. Any internal exception becomes a positioned
compiler error — never a silent success.

**Enabling.** Verification happens only when the plugin is enabled by the build:

```scala
Compile / scalacOptions += "-Xplugin:" + pluginClasspath
```

The head entry of that classpath must be the plugin JAR (it carries
`plugin.properties`); the remaining entries are the plugin's runtime
dependencies. See `sroofPluginClasspath` in `build.sbt`.

## 7. Translation into core

### Inductives

A supported enum becomes an `IndDef`. Cases come from the compiler's `children`,
sorted by source offset so constructor order is exactly declaration order — which
is what `Term.Mat` branch positions mean. Strict positivity is checked by the
existing `PositivityChecker`.

### Definitions

A `def` becomes a `DefEntry` whose body is always `Fix`-wrapped, recursive or
not, matching what the legacy elaborator produces:

```text
def f(a: A, b: B): C = body
  ⇒  tpe  = Pi(a, A, Pi(b, B, C))
     body = Fix(f, tpe, Lam(a, A, Lam(b, B, ⟦body⟧)))
```

De Bruijn conventions, stated once because they are the easiest thing to get
backwards:

- parameters enter the scope **reversed** — for `f(a, b)`, `b` is `Var(0)` and
  `a` is `Var(1)`;
- match field binders also enter **reversed** — in a branch for `C(x, y)`, `y` is
  `Var(0)` and `x` is `Var(1)`;
- self-reference is `Var(scope.length)`: the `Fix` binder sits immediately
  outside all lambdas and all match binders, so it is always one past the
  innermost scope.

Core `Term` has no global-reference node, so a call to another definition is
**inlined** as that definition's translated body. Translated bodies are closed,
so no shifting is involved. `TerminationChecker` runs on every definition.

**Definition ordering.** Scala allows forward references between methods, so
definitions are scheduled by dependency rather than by source order. Direct
self-recursion is fine; any cycle involving two or more definitions is mutual
recursion and is rejected with the participants named.

**No fallback metavariables.** Every supported type is a closed
`Ind(name, Nil, Nil)`, which lets the expected type be threaded top-down and used
verbatim as a `Mat` return type. No accepted translation contains a `Meta` node;
`CoreTranslatorSuite` asserts this. (Widening the type language means revisiting
the threading — the expected type would then need shifting under binders.)

**Equality goals** use the 2-argument encoding `App(App(Ind("Eq"), lhs), rhs)`.
That is deliberate, not a shortcut: it is the form `Bidirectional.inferUniverse`
recognises as Prop-level and the form `infer` produces for `refl`. The 3-argument
form cannot be typed by the existing checker, since `Ind("Eq", …)` is a built-in
absent from `GlobalEnv` and so has no `Pi` type to apply. `Eq.mkPropType` is the
single definition of this encoding.

## 8. Proof execution and the kernel gate

For each `@theorem`, in source order:

1. parameters become a `Context` (left to right, so the last parameter is
   `Var(0)`) and the goal is translated in the reversed scope;
2. the tactic script runs through the existing `TacticM`/`Builtins`, producing a
   *candidate* term;
3. the candidate is closed over the parameters into a full `Lam`, and the goal
   into the matching full `Pi`;
4. `Kernel.verify(Context.empty, fullProof, fullProp)` decides;
5. only on success does the theorem enter `GlobalEnv` as a `DefEntry`, and only
   then does a `@simp` theorem enter `simpSet`.

Step 5 is what keeps proof reuse honest: an unproved or rejected theorem never
reaches the environment, so it cannot be cited by a later proof.

`induction` maps onto `Builtins.induction`, which chooses between a plain `Mat`
and a `Fix`-wrapped proof by comparing each branch's binding count against the
constructor arity. The frontend appends the reserved binding name `ih` for
branches that used `ih(...)`, which is what requests the hypothesis.

There is no `sorry`, no `skipKernel`, no warning-only mode, and no fallback proof
on this path. The legacy `.sroof` path keeps its `sorry` support; the Scala path
never had it.

## 9. Trust and semantic correspondence

See [trust-model.md](trust-model.md) for the full statement. In short, the Scala
path makes two distinct claims:

- **Core logical validity** — decided by the kernel, checker, and evaluator,
  exactly as on the `.sroof` path. Tactics remain untrusted generators.
- **Scala semantic correspondence** — the claim that the core model *is* the
  Scala program. This rests on `scala-frontend`'s translation and on the
  plugin's extraction, both of which are therefore inside the trusted computing
  base for that claim.

The bridge is kept small and conservative, and is backed by golden translation
tests, a finite differential test comparing Scala `plus` against core evaluation,
and negative tests ensuring unsupported Scala is rejected rather than
mistranslated.

## 10. Migration from `.sroof`

The `.sroof` path is a supported legacy path, not a deprecated one. Nothing about
it changed in this milestone: the parser, elaborator, CLI (`check`, `agent`,
`extract`, `repl`), stdlib, examples, VS Code extension, sbt plugin, and Scala
Native binary all behave as before.

Planned sequence:

1. **now** — both paths coexist; the Scala path covers the `nat.sroof` slice.
2. **next** — the Scala path grows until it covers the stdlib's proof patterns.
3. **later** — `sbt-sroof` gains a mode that injects `scala-api` and the compiler
   plugin instead of extracting generated Scala (see below).
4. **eventually** — the legacy parser is removed once the Scala path reaches
   parity and users have migrated. Not before.

### `sbt-sroof`

The existing nested sbt plugin is **legacy integration**: it drives the `.sroof`
CLI and its extraction workflow, and is unchanged. A future mode that adds
`scala-api` as a dependency and the compiler plugin to `scalacOptions` is
designed but not implemented, because it cannot be tested honestly until the
artifacts are published. `build.sbt` shows the shape such a mode would take.

## 11. Future work

- **Indexed families / GADTs** — `Vec`-style indexed types, as the `.sroof` path
  already supports.
- **Richer tactic DSL** — `calc`, `apply`, `have`, and the rest of the built-ins
  the `.sroof` path exposes. `cases` and `rewrite` landed in v0.4.
- **Induction hypotheses for non-final recursive fields** — the tactic engine
  applies the recursion to `Var(0)`, so `ih` is only available for a
  constructor's last field. Targeting a chosen field needs a change in
  `Builtins`, not in the frontend.
- **Nested patterns** — `case Succ(Succ(k))` would have to be desugared into
  nested `Mat`s, and the desugaring has to redistribute the sibling branches to
  stay exhaustive. Deferred because getting it subtly wrong is invisible to the
  kernel.
- **Cross-JAR theorem metadata** — today a lemma must be a theorem verified
  earlier in the same module; sharing across compilation units needs proof
  metadata in TASTy or a sidecar.
- **Incremental verification** — re-verifying only modules whose proof-relevant
  content changed, in the spirit of `INCREMENTAL_CHECKING.md`.
- **Numeric primitives** — deliberately modelled, rather than assumed.
