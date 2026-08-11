# Changelog

All release detail lives here. Earlier releases also had per-version
`RELEASE_NOTES_v*.md` and `RELEASE_CHECKLIST_v*.md` files; those were removed in
favour of this one file. The long-form notes for v0.3–v0.9 remain published on
the [GitHub releases page](https://github.com/kmizu/sroof/releases).

## [0.23.0] - 2026-08-12

The third time the same defect shipped, and the test that should stop a fourth.

### Fixed
- **`sroof extract` emitted code from a file `sroof check` rejects.** Extraction goes
  through the cached path (`processSourceWithIncrementalStats`), which ran the proof
  phase but not `#check`. A file whose `#check` does not type-check was rejected by
  `sroof check` and extracted happily by `sroof extract`. The cache key already
  covered the checks, so the outcome is now computed and cached with the rest.
- `sroof extract` prints `sorry` warnings to stderr. Extraction erases proofs, so a
  `sorry` does not make the emitted code wrong — but "extract from a verified file"
  is what the command claims, and a file with a `sorry` in it is not one.

### Added
- `cli/EntryPointAgreementSuite` — the same six sources through all six entry points
  into the pipeline, asserting they agree in both directions. The accepting half is
  not decoration: an entry point that rejected everything would pass the rejecting
  half on its own. It fails on the previous tree, naming the three paths that
  disagreed.

## [0.22.0] - 2026-08-11

The rest of the REPL. Having tests for it turned up two more.

### Fixed
- **`#check` printed nothing in the REPL.** The result was computed and dropped, and
  the session printed its environment summary as though nothing had been asked.
- **An ill-typed `#check` was accepted in the REPL.** `#check Nat.succ(Bool.tru)`
  reported OK. Files stopped doing this in v0.15; the REPL is a second path through
  the same pipeline and kept doing it. `processDeclaration` now runs
  `Checker.evalChecks` and reports both the type and the failure.

### Added
- `ReplSuite` cases for `#check` (good, ill-typed, unknown name) and for `defspec`
  (proved, and a false one rejected).

## [0.21.0] - 2026-08-11

The REPL, which had no tests, and the proof agent, which had one.

### Fixed
- **`sroof repl` never returned at end of input.** `readMultiLine` reported both a
  blank line and end of input as `""`, and the loop ignores blank input — so
  `sroof repl < script.sroof`, or any closed stdin, printed a prompt and read again,
  forever, at about a megabyte of prompts a second. The reader now returns
  `Option[String]` and `None` ends the session.
- **The REPL's accumulated environment was never seen by elaboration.**
  `processDeclaration` threaded a `GlobalEnv` from entry to entry, but
  `Elaborator.elaborate` always started from `GlobalEnv.empty`, so a `def` could not
  mention an `inductive` declared one line earlier — `Unknown inductive type or
  struct variable: Nat`. `elaborate` now takes the environment to start from; a file
  still starts from nothing.

### Added
- `cli/ReplSuite` — the reader and the loop, driven from a script instead of a
  terminal. Every fake reader fails the test rather than returning `null` forever, so
  a regression to the loop above shows up as a failure and not a hung build.
- `cli/agent/FileRepairerSuite` — what `sroof agent` writes back: that the repaired
  file parses and verifies, that a false statement is left as `sorry` rather than
  "repaired", and that a partial repair keeps exactly the sorries it could not close.
  These pass on the previous tree; the agent was correct, and this is the coverage it
  did not have.

### Changed
- `MainSuite`'s "readMultiLine: single-line input terminates after one non-empty
  line" said in its own body that stdin could not be tested, and called
  `processSource` instead. It never touched the reader. Renamed to what it does; the
  reader is now tested for real in `ReplSuite`.

## [0.20.0] - 2026-08-11

Extraction. v0.19 measured the gap — 8 of the 26 shipped `.sroof` files extracted
to Scala that compiles — and named one cause. Sweeping the corpus properly turned
up **five** independent defects, and the one v0.19 named was not the largest.

**All 26 files now extract to Scala that compiles**, and three of them are compiled
*and run* against expected answers.

### Fixed
- **A recursive def was pasted in at every use site.** The core has no node for
  "reference to a global definition" — the elaborator inlines the body — so
  extraction emitted a full copy of `plus` inside every function that called it, in
  expression position, as `{ def plus … ; plus }(x)(y)`. That does not parse. Bodies
  are now matched back to their definitions and emitted by name.
- **A `Fix`-shaped body peeled no parameters.** `peelLambdas` stops at a `Fix`, so a
  recursive def stayed a *value* whose type was rendered as a type lambda:
  `def concat: [A <: Any] =>> [n <: Nat] =>> …`. Unwrapping the `Fix` first puts the
  parameters back in the signature.
- **`Type`-valued parameters stayed value parameters** — the defect v0.19 named.
  `def poly_length(A: Type, xs: PolyList(A))` now extracts as
  `def poly_length[A](xs: PolyList[A]): Nat`, including at recursive call sites,
  which apply the `Fix` binder rather than anything the global map would recognise.
- **Index arguments were erased from `enum` cases but not from constructor
  applications or match patterns**, so a declaration taking two arguments was used
  with three. They are no longer erased at all: an index is ordinary runtime data,
  and it is what a length-taking function is passed. Only *proofs* are erased, and
  now consistently in all three places.
- **A parameterless case in an invariant generic enum** cannot fix its type argument
  (`cannot determine type argument for enum parent class`). Generic enums are emitted
  covariant when no constructor field is a function type.
- **An unresolved `Var` rendered as `T0`.** A name that is declared nowhere fails
  with `Not found`; it is now `Any`, which is at worst too weak.
- **A proof-carrying record emitted its proof field**, naming types that do not exist
  in the extracted program (`arg1: Eq[isValidCodepoint, Bool]`). Proof fields are
  dropped — which is the erasure the extractor always claimed to do.
- **Two records may both call their constructor `mk`**, and both wildcard imports are
  in scope: `Reference to Mk is ambiguous`. A pattern now names its inductive, taken
  from the scrutinee's type.
- **`Int.pos(n)` became `n + 1` regardless of what `n` was.** In `examples/int.sroof`
  the payload is a `Nat`, so the match bound an `Int` for a branch expecting a `Nat`.
  The arithmetic mapping now applies only when the program does not build or take
  apart values of that type — which keeps `stdlib/Effect.sroof`, whose IO runtime
  needs a real `Int`, working exactly as before.

### Added
- `scala-it/ExtractionRuntimeSuite` — compiles the extracted Scala **and runs it**.
  Addition, polymorphic list append/reverse/length, and vector concatenation are
  checked against expected values. Compiling is a weak bar: an extractor that
  swapped a constructor's two arguments would compile just as happily. Two of the
  three cases fail on the v0.19 tree.
- `CompilerHarness.compileAndInvoke`, which loads the compiled classes and calls
  into them.

### Changed
- `ExtractionCorpusSuite` now asserts that *every* shipped file compiles; its
  exception list is empty, and a second case fails if that list ever names a file
  that is not in the corpus.
- `ExtractorSuite`'s hand-built `Vec` fixture used the wrong De Bruijn convention: it
  omitted the constructor's own preceding arguments from the scope of a later
  argument's type. The extractor omitted them too, so the two agreed and the tests
  passed. `stdlib/Vec.sroof` shows the real shape, and the fixture now matches it.

### Not fixed
- Extraction is still whole-program and per-file; there is no module system, so a
  file that imports another re-extracts everything it imported.

## [0.19.0] - 2026-08-11

A measurement. v0.18 fixed two defects that made *every* extraction invalid;
sweeping the whole shipped corpus afterwards showed the rest of the gap.

**8 of the 26 shipped `.sroof` files extract to Scala that compiles.**

### Found
The 18 that do not fail for one dominant reason. A `.sroof` definition takes its
type parameter as an ordinary `Type`-valued parameter — `def poly_length(A: Type,
xs: PolyList(A))` — and `Extractor.termToScalaType` renders the resulting
unresolved `Var(i)` as the literal name `T0`, `T1`, …, a type that is never
declared:

```
E.scala:21: Missing type parameter for [A] =>> PList[<error Not found: type T0>]
```

The fix is to promote `Type`-valued parameters to Scala type parameters, so that
`poly_length` extracts as `def polyLength[A](xs: PList[A]): Nat`. That is a real
feature rather than a patch, and it is not in this release.

### Added
- `ExtractionCorpusSuite`, pinning both halves: the eight files that compile must
  keep compiling, and the count that do not must not grow. It is written so that
  *fixing* the gap also fails the test and forces the lists to be updated — a
  measurement, not an endorsement.
- `docs/stdlib.md` records the status and the diagnosis.

Proof checking is unaffected throughout; this is the extraction back end only.

## [0.18.0] - 2026-08-11

**Extracted Scala did not compile.** `sbt "cli/run extract ..."` is a documented
command and a headline claim — the verified artifact and the shipped artifact are
meant to be the same object — and its output had not been valid Scala for a long
time.

### Fixed
- **Match patterns were emitted as `case _.Zero`.** `_` is not a stable
  identifier, so every extracted `match` was a syntax error. `extractProgram` now
  emits `import <Enum>.*` after each enum and the patterns use the bare
  constructor name.
- **A `Fix` was rendered as `def f: Any = …`.** `termToScalaExpr` destructured
  `Term.Fix(name, _, body)`, discarding the declared type, so the recursive call
  inside the body was an application of an `Any` and did not typecheck. The
  declared type is now used.

### The reason it shipped
`ExtractorSuite` asserts on **substrings** — `contains("enum Nat:")`,
`contains("case _.Zero")`. Nothing ever handed the result to a compiler, and one
test was actively pinning the broken output.

`ExtractionCompilesSuite` now extracts from real `.sroof` source, compiles the
result with dotc, and **runs** it. Its `sub` is deliberately asymmetric — it
matches on its second argument and returns its first — so an extraction that
swapped them would still compile and the runtime assertion would catch it.

The substring test that required `case _.Zero` now requires the opposite, and
asserts `_.` appears nowhere.

### Verification
649 tests. Both new cases fail on the v0.17 tree. `scalaIt` gains a test-scoped
dependency on `extract` and `syntax` so the suite can call the extractor rather
than pin a golden string that would rot.

## [0.17.0] - 2026-08-11

Multi-step `calc` never worked. That is the headline; the rest of the release is
a sweep that found it.

### Fixed
- **A `calc` chain of more than one step was always rejected.** Two mistakes in
  the transitivity term, both in `Checker.buildTransProof`:

  - It was handed the midpoint **term** where the motive needed that value's
    **type**, producing a binder whose declared type is a value: `λy:Nat.zero. …`.
  - The motive body used the 3-argument `Eq` form with a `Meta` element type.
    `inferUniverse` does not recognise that form, and the evaluator refuses a
    `Meta` outright, so the motive could not even be reduced.

  Together they produced a beta-redex the checker could not touch:

  ```
  expected: ((λy:zero. (((Eq ?-1) zero) y)) zero)
  actual:   ((Eq zero) zero)
  ```

  A single-step chain returns before reaching that code, which is why the tactic
  looked like it worked. The type is now inferred and the 2-argument `Eq` form
  used throughout.

- **`programHashFor` omitted inputs that change the outcome**: constructor return
  indices (which decide typing as of v0.10), each definition's declared type
  (checked as of v0.14), the `@[simp]` set, structures and operators.

  The surface-AST hash upstream catches every source edit on its own, so nothing
  was observably wrong — probing confirmed a changed return index and a changed
  declared type are both re-checked. But this function reads as *the* invalidation
  key, and an input it omits is a landmine for whoever relies on it next.

### Added
- `CalcSuite`: five cases, including a chain whose steps do real work rather than
  `zero = zero` twice, and two soundness cases — a step that does not hold, and a
  chain that does not reach the goal.
- Two `IncrementalSuite` cases pinning cache invalidation across a return-index and
  a declared-type change.

### Probed and found correct
Every logic tactic — `tauto`, `decide`, `contradiction`, `assumption`,
`constructor`, `left`, `split`, `repeat`, `try`, `all_goals`, `first`, `skip` —
rejects a false statement. `try` and `skip` in particular do not leave a goal open
and call it proved.

The incremental cache is sound: a changed constructor return index and a changed
declaration type are both re-checked, because the surface-AST hash invalidates
everything downstream.

### Verification
647 tests. The two multi-step `calc` cases fail on the v0.16 tree; the soundness
cases are rejected on both, which is what they are for.

All 640 pre-existing tests pass unchanged.

## [0.16.0] - 2026-08-11

A release about the **trusted bridge** — the part of sroof the kernel cannot check.
`CoreTranslator` and `TreeExtractor` decide what core proposition a Scala theorem
is about, so a bug there hands the kernel a valid proof of a different statement
and nothing downstream notices.

One defect found, and the rest of the bridge probed and confirmed faithful.

### Fixed
- **A GADT-shaped enum was accepted with its index silently dropped.**

  ```scala
  enum Vec[A, N]:
    case VNil[A]()                       extends Vec[A, Zero.type]
    case VCons[A, M](h: A, t: Vec[A, M]) extends Vec[A, Succ]
  ```

  `InductiveExtractor` instantiates every case's constructor at the *enum's* own
  type parameters — which is what makes ordinary generic enums work — so both cases
  came out as constructors of a uniform `Vec[A, N]`.

  Not unsound: Scala's typer still enforces the indices on the Scala side, and the
  core reading is the weaker parametric one, so the failure mode is a rejected proof
  rather than a false one. But the bridge's stated rule is to refuse what it cannot
  carry, precisely because nothing downstream can notice, and dropping an index is
  an approximation. It now refuses, naming the fixed type argument and pointing at
  the `.sroof` path, which does support indexed families.

### Added
- **`scala-it/BridgeFidelitySuite`** — nine cases asserting the bridge means what
  the Scala says. Each is a **false** statement built out of one construct: if the
  construct is translated faithfully the statement stays false and compilation
  fails; if it is mistranslated the statement may become true and compile. Every
  false case is paired with a true control, since a bridge that rejected everything
  would pass the false half on its own.

  Covered: argument order (via a deliberately asymmetric `sub`), nested
  application, `val` bindings, default arguments both omitted and explicit, and the
  refusal of lambdas, side effects and `if`/`else`.

### Probed and found correct
Argument order is preserved. `val` bindings keep their definitions. A default
argument supplies the declared default, omitted or not. Lambdas, `println` and
`if`/`else` are refused rather than approximated — `if`/`else` in **both**
directions, which is the point: an unsupported construct is refused, not
approximated into something that happens to agree on the example at hand.

No mistranslation was found. Eight of the nine new cases pass on the v0.15 tree
too, which is the honest reading: they document that the bridge was already
faithful, and they are worth keeping because nothing else guards it.

### Verification
632 tests. The GADT case fails on the v0.15 tree; the other eight are fidelity
guards rather than evidence of the change.

All 631 pre-existing tests pass unchanged, including the generic-enum suites — the
control asserting an ordinary `enum Box[A]` is still accepted exists because a
check that rejected every generic enum would have passed the GADT case.

## [0.15.0] - 2026-08-10

Step 5, and three failures that were being swallowed.

**`stdlib/Vec.sroof` now carries its length in the type.** `concat`'s return type
is the theorem, and there is no separate lemma to prove:

```scala
def concat(A: Type, n: Nat, m: Nat, xs: Vec(A)(n), ys: Vec(A)(m)): Vec(A)(plus(n, m))
```

Since v0.14 a `def` body is kernel-checked, so that is verified rather than
declared. `StdlibSuite` asserts that replacing it with `Vec(A)(Nat.zero)` makes the
file stop checking — the only way to know the type is load-bearing. The file also
proves `vlen_is_index` by induction, exercising the v0.13 machinery on shipped code.

That completes steps 1–5 of `docs/indexed-families.md`. Only the Scala frontend
(GADTs) remains.

### Fixed
- **A `#check` that does not type-check no longer reports OK.** The error string was
  computed, the plain CLI never printed it, and the file passed — so
  `#check Nat.succ(Bool.tru)` was completely silent. A `#check` is an assertion the
  author wrote: it now fails the file, and successful ones print their type.

- **The JSON path disagreed with the CLI about the same file.** It flagged the
  individual check as `ok:false` while the document still said `ok:true`, so tooling
  and the exit code gave different answers. One shared `Checker.evalChecks` now
  backs both; the per-check flags stay, since that detail is what the JSON is for.

- **`simplify` ignored an unknown lemma name.** `tryGlobalLemmaAsIH` fell back to
  `trivial`, so a typo was silent whenever the goal closed anyway — and on a goal it
  could not close, the error pointed at the *goal*, sending you to debug the proof
  instead of the spelling. Unknown names are now named:

  ```
  simplify: unknown lemma 'ih_typo' — not a hypothesis in scope and not a
  definition or proved lemma. Check the spelling.
  ```

  Only names the author wrote are checked; the default `simpSet` comes from
  `@[simp]` annotations on definitions that exist by construction.

None of the three was unsound — the kernel always had the final say. They were bad
in a different way: each sent you to look at the wrong thing.

### Verification
631 tests. Five of the seven new cases fail on the v0.14 tree, plus the new
`StdlibSuite` case.

The JSON test asserts on the document's *opening* rather than using `contains`: the
first version matched the per-check `"ok":false` inside the checks array and passed
on the very tree it was meant to reject.

All 623 pre-existing tests pass unchanged.

### Probed and found correct
Strict positivity rejects `inductive Bad { case mk(f: Bad -> Bad): Bad }`; the
termination checker rejects a non-structural recursive call; `have`, `exact` and
`rewrite` all reject what they should. `structure`/`instance` field mismatches are
now caught too — as a side effect of v0.14, since an `instance` desugars to a `def`.

## [0.14.0] - 2026-08-08

A bug-hunting release. The headline is that **`def` bodies are now checked against
their declared types** — until now nothing did, and this was accepted:

```scala
def f(n: Nat): Nat { Bool.tru }
```

Only a `defspec` reached the kernel, and every proposition is written in terms of
definitions. Turning the check on immediately found five real defects in the
shipped stdlib and examples, and closed a crash.

### Fixed
- **`def` bodies are kernel-checked** (`Checker.checkDefBodies`), before proofs: a
  proposition built from a definition that does not type-check is not worth a proof
  error about.

- **Five broken definitions in the shipped corpus.** `stdlib/PolyList.sroof`'s
  `poly_length`, `poly_append` and `poly_reverse`, plus `concat` in both
  `stdlib/Vec.sroof` and `examples/vec.sroof`, declared their type parameter *last*.
  That forces a bare `PolyList`/`Vec` in the signature where the value has the
  applied type — the exact anti-pattern PolyList's own header warns against, and
  which v0.7 worked around by adding a correct `PList` beside the broken originals
  instead of fixing them. Their signatures now take the type parameter first.

- **A `p`-wide substitution window for a family that declares indices.**
  `Elaborator.elabInductive` puts `(params ++ indices)` in scope when it elaborates
  constructor argument types — *unconditionally*, whether or not the constructors
  state their indices. Substituting with a parameters-only spine therefore lands
  every parameter one slot per index off: for the phantom `Vec(A)(n)`, `head: A` was
  left dangling while the index slot was overwritten with `A`. `IndChecker.paddedSpine`.

- **An evaluator failure crashed the CLI with a stack trace.** `Eval` throws on an
  unbound index, a match with no branch for the value's constructor, or an
  application of a non-function. Reaching users needed nothing exotic — passing
  arguments in the wrong order did it, via
  `RuntimeException: Non-exhaustive match: no case for constructor 'tru'`.

  `Bidirectional.whnf`, `convCheck`, `Kernel.check` and `Checker.executeProof` now
  each turn it into a rejection. Every catch is rejection-safe by construction: an
  unreduced term is strictly less likely to match, and a term the evaluator cannot
  reduce is equal to nothing. An exception can lose a proof, never manufacture one.

### Step 5 is unblocked
A dependently-typed definition's return index is now verified, so this is a checked
claim rather than a comment:

```scala
def vapp(A: Type, n: Nat, m: Nat, xs: Vec(A)(n), ys: Vec(A)(m)): Vec(A)(plus(n, m)) { … }
```

There is no separate lemma — the theorem *is* the type. It is in
`examples/vec_indexed.sroof`, and changing the return type to `Vec(A)(Nat.zero)`
makes that file stop checking (verified, not asserted). Converting
`stdlib/Vec.sroof` itself is now a matter of rewriting a shipped signature.

### Verification
623 tests. Five of the seven new cases were run against the v0.13 tree and **fail**
there — and the crash case fails by actually throwing
`java.lang.RuntimeException`, which is the clearest form the evidence could take.

A corpus test checks every shipped `.sroof` file, so the five definitions cannot
regress. All 616 pre-existing tests pass unchanged.

### Also corrected
`CLAUDE.md` still described `CtorDef.retIndices` as "a stub — nothing writes it",
which stopped being true in v0.8 and stopped being harmless in v0.10. The
`stdlib/Vec.sroof` header still described the parser as unable to express an
indexed return type. Both now say what the code does.

## [0.13.0] - 2026-08-08

Step 4 is finished. `induction` over an indexed family now carries a working
induction hypothesis, so this is provable — and the `vlen` here is the recursive
one, which is what makes the hypothesis necessary:

```scala
def vlenr(A: Type, n: Nat, v: Vec(A)(n)): Nat {
  match v {
    case Vec.vnil           => Nat.zero
    case Vec.vcons(m, h, t) => Nat.succ(vlenr(A, m, t))
  }
}

defspec vlenr_correct(A: Type, n: Nat, v: Vec(A)(n)): vlenr(A, n, v) = n {
  by induction v { case vnil => trivial  case vcons m h t ih => simplify [ih] }
}
```

### Added
- **`Builtins.inductionIndexed`.** `_rec` has to accept the tail, whose index is
  `m` and not the scrutinee's `n`, so the `Fix` binds the index *before* the vector
  it describes:

  ```text
  Fix(_rec, Pi(_i, Nat, Pi(_n, Vec A _i, P(_i)(_n))),
    Lam(_i, Nat, Lam(_n, Vec A _i, Mat(Var(0), cases, P))))
    applied to (idx, scrutinee)
  ```

  Each branch specialises `_i` to that constructor's declared index, and the
  hypothesis is `_rec` applied to the recursive argument's index and the argument.
  In the `vcons` branch `ih` is `vlenr(A, m, t) = m` — about the tail, which is
  what `simplify` can use.

  A separate path rather than an extension of `inductionWithIHGeneralized`, which
  binds `_n` outermost: there the scrutinee type's mention of the index would still
  point at the outer context. Every existing induction shape is untouched.

  Fires only when the scrutinee's index argument is a plain context variable, the
  index type is closed, and there is exactly one index. Anything else takes the
  ordinary path. Two indices would need the Pi chain built in intermediate
  contexts, since the second index's type may mention the first.

### The bug worth recording
The first attempt built the motive with `computeGeneralizedMotiveBody`, which
*removes* its pivots from the context. The kernel rejected it:

```
expected: Type
actual:   ((Vec #3) #2)
```

The proof term is placed in `goal.ctx`, so a removed-variable context only agrees
with it when every entry the branches mention is newer than what was removed —
and `A` is declared before both the scrutinee and the index. This is exactly
coordinate rule 2 from v0.7, rediscovered. Everything is now stated in `goal.ctx`.

### Verification
616 tests. The two acceptance cases were run against the v0.12 tree and **fail**
there. Three soundness cases — `n = Nat.zero`, `n = Nat.succ(n)`, and
`Nat.zero = Nat.succ(Nat.zero)` — are rejected on both trees; `n = succ n` earns
its own case because a hypothesis wired to the wrong index would close it.

All 611 pre-existing tests pass unchanged.

### Step 5 is blocked, and no longer by the tactic engine
A `def` body is not type-checked at all. Both of these are accepted today:

```scala
def f(n: Nat): Nat { Bool.tru }
def vapp(A: Type, n: Nat, m: Nat, xs: Vec(A)(n), ys: Vec(A)(m)): Vec(A)(Nat.zero) { … }
```

Only a `defspec`'s proposition and proof reach `Kernel.verify`. A length-preserving
`vapp` would therefore *declare* `Vec(A)(plus(n, m))` with nothing checking that it
delivers one — a declaration promising a length no one verifies, which is worse
than the phantom index it would replace. `stdlib/Vec.sroof` stays as it is.

This is pre-existing and has nothing to do with indexed families; it simply becomes
the binding constraint now that step 4 is done. Step 5 starts by kernel-checking
`def` bodies.

## [0.12.0] - 2026-08-07

Half of step 4. Case analysis over an indexed family now **learns the index**, so
this is provable — the first theorem in the project about an arbitrary vector
rather than a particular one:

```scala
defspec vlen_matches_index(A: Type, n: Nat, v: Vec(A)(n)): vlen(A, n, v) = n {
  by cases v { case vnil => trivial  case vcons m h t => trivial }
}
```

Matching `vnil` out of a `Vec(A)(n)` tells the branch that `n` is `Nat.zero`, so
the goal there becomes `vlen(A, zero, vnil) = zero` instead of the unprovable
`vlen(A, n, vnil) = n`.

### Added
- **Per-branch index refinement** (`IndChecker.indexRefinement`). Within the
  branch for constructor `c`, the scrutinee *is* `c(args)`, so the scrutinee's
  index and `c`'s declared index are the same thing. Refining is exactly
  abstracting the return type into a motive over the index and applying it at each
  constructor's index — the ordinary dependent-match rule.

  Both `IndChecker.checkCases` and `Builtins.specializeGoal` use the one rule, so
  the sub-goal a user is shown is the one the kernel will ask for. Getting those
  out of step would build proofs against a proposition the kernel never checks.

  It fires only when the scrutinee's index argument is a plain **variable**.
  `v : Vec A (succ k)` refines nothing: deciding `vnil` is unreachable, or that
  `succ k ≡ succ m` gives `k ≡ m`, needs real unification, and guessing inside the
  TCB is not worth a convenience. The unrefined branch is strictly harder to
  prove, so the cost is a false negative.

### Fixed
- **`Bidirectional.infer` gave an indexed family the wrong arity.** It folded
  `Ind` over parameters only, so `Vec(A)(n)` in a *binder* position failed with
  `Expected function type, got Type for (Vec #1)`. A theorem could state an index
  but no definition could take one as an argument — `def vlen(A, n, v: Vec(A)(n))`
  was unstatable. `Vec : Type → Nat → Type` now.

  Gated on `isIndexed`, so a family that declares indices without stating them on
  its constructors keeps the shorter arity. `stdlib/Vec.sroof` writes
  `tail: Vec(A)`, which the wider arity would reject.

### Verification
611 tests. Four of the new cases were run against the v0.11 tree and **fail**
there: the two acceptance tests, the binder test, and the assertion that the
false claim fails *in the `vcons` branch* specifically.

That last one is the soundness test. `n = Nat.zero` is false, and refinement does
make its `vnil` branch close — the check is that `vcons` becomes `succ m = zero`
and does not. Refining one branch must not excuse the others. An absurd equation
(`zero = succ zero`) and a concrete-index scrutinee are covered too.

All 605 pre-existing tests pass unchanged.

### Not in this release
- **The induction hypothesis.** `_rec` has to accept the tail, whose index differs
  from the scrutinee's, so the `Fix` must bind the index *before* the vector it
  describes:

  ```text
  needed:  Fix(_rec, Pi(i, Nat, Pi(_n, Vec A i, P(i)(_n))), …)
  today:   Fix(_rec, Pi(_n, varTpe, genPiBody), …)
  ```

  `inductionWithIHGeneralized` already generalises over context variables but
  binds `_n` outermost, so `varTpe`'s mention of `n` still points at the outer
  context. Reordering moves the Lam nesting, the `Mat` scrutinee position, the
  application order, and every coordinate in `genSpecializeGoal`.

- **`stdlib/Vec.sroof` still uses a phantom index**, for the same reason: it would
  declare a length it could not prove anything recursive about.

## [0.11.0] - 2026-08-07

Two things that were **written down wrong**: a proof state that misrendered every
dependent hypothesis, and a comment claiming the checker's typing rules are
outside the trusted computing base when the kernel runs on them.

Both were found while scoping induction over indexed families (step 4), and both
had to be fixed before that work is worth starting — you cannot debug De Bruijn
arithmetic against a printer that is itself off by one.

### Fixed
- **`ProofStatePretty.formatContext` rendered each hypothesis's type against a
  name list that included the hypothesis itself.** Every De Bruijn index in a
  dependent type therefore resolved one binder too late, and `v : Vec A n`
  printed as `Vec n v` — a hypothesis appearing inside its own type, which cannot
  happen. The recursor was worse: `_rec` showed a motive over the wrong variables
  entirely.

  The old code was justified by a comment claiming some tactics pre-shift the
  types they store, and that "the extra name at position 0 simply goes unused".
  The second half only holds for a *closed* type — which every hypothesis in the
  test suite was, until indexed families arrived. The entries `induction` creates
  (`_rec`, `_n`) were checked directly and render correctly under the corrected
  form.

  ```
  before:  (hyp "v" "((Vec n) v)")
  after:   (hyp "v" "((Vec A) n)")
  ```

### Changed
- **`IndChecker` is now documented as being inside the TCB, because it is.** Its
  header said "This module is NOT part of the trusted kernel. Every proof term it
  produces is re-checked by `Kernel.check`." `Kernel.verify` delegates to
  `Bidirectional.check`, which calls straight into `IndChecker` — the kernel
  re-checks a proof term *using* these rules, so it cannot catch a bug in them.
  The v0.10.0 constructor-index unsoundness lived here for seven releases and the
  kernel accepted it every time.

  `docs/trust-model.md` had it right but did not name `IndChecker`, leaving
  "everything in `checker/` except `Bidirectional` is re-checked" as an available
  and wrong reading. It is now named on both lists explicitly.

### Added
- A `ProofStateSuite` case asserting a dependent hypothesis type renders in the
  scope outside that hypothesis. Verified to **fail** on the v0.10 tree. 605 tests.
- `docs/indexed-families.md` records the measured proof state for induction over
  an indexed family: the scrutinee is replaced by the constructor but the index is
  not, so the `vnil` branch asks for `vlen A n vnil = n` where it should ask for
  `vlen A zero vnil = zero`. `induction v generalizing n` does not help —
  generalising a context variable is not the same as tying it to the constructor's
  declared index. That is step 4, and it is next.

### Not in this release
- **Step 4 itself.** The induction machinery in `Builtins` runs to roughly 500
  lines across six mutually-dependent helpers, and this project does not ship
  delicate De Bruijn work it has not validated end to end. What it ships instead
  is the observation that work starts from, and a printer that can be trusted
  while doing it.

## [0.10.0] - 2026-08-07

Indexed families stop being decorative. `Vec(A)(n)` now has a length the checker
enforces — and closing that gap meant fixing an unsoundness, not just adding a
feature.

### Fixed
- **A constructor's index was taken from the expected type instead of from its
  declaration.** `IndChecker.inferConWithParams` ended by applying the inductive
  to `paramVals` — which `extractParamsFromExpected` had peeled off the *expected*
  type. For a parameterised type like `List(A)` that is harmless, since a
  parameter has the same value in every constructor. For an indexed type it means
  the constructor's inferred type *is* the expected type, so the caller's
  conversion check compared the expected type with itself and accepted anything.

  This checked successfully on every release through v0.9:

  ```scala
  defspec vnil_is_not_length_one: Vec(Nat)(Nat.succ(Nat.zero)) { Vec.vnil }
  ```

  A length-zero vector passed as a length-one vector. It is now rejected with
  `expected: ((Vec Nat) (succ zero)) / actual: ((Vec Nat) zero)`.

  The parameter half of the spine is still read off the expected type, exactly as
  before. The index half is derived from the constructor's declared `retIndices`,
  populated since v0.8 and until now read by nothing.

- **`extractParamValsFromArgs` scanned a window of the wrong width.** In an
  indexed family the indices occupy De Bruijn slots *between* the constructor's
  arguments and the type's parameters, so a `params.length`-wide window reads a
  parameter out of an index's slot — and leaves the parameter variables past the
  end, where they fall through to `Eval` as free variables. This is what produced
  v0.8's `Unbound De Bruijn index 2 (env size 0)` and caused that attempt to be
  reverted. The width is now a parameter: `p` for an ordinary inductive, `p + q`
  for an indexed one.

- **`Term.show` dropped a constructor's arguments.** Harmless until indices could
  differ, at which point a mismatch rendered as
  `expected: Vec Nat succ / actual: Vec Nat succ` and read like a checker bug.

### Added
- A constructor whose return index mentions one of the family's *own* index
  variables — `case anylen: Bad(A)(n)` — is rejected, naming the declaration
  rather than the use site. Such a declaration would reintroduce exactly the
  vacuity above.
- `examples/vec_indexed.sroof`: a `Vec` with real indices, and the rejected
  variants recorded as comments.
- `cli/.../IndexedFamilySuite.scala` and four cases in `IndCheckerSuite`.
  603 tests pass, up from 590.

### Verification
Each negative test was run against the v0.9 tree and **fails** there — four of
the five were accepted as valid proofs. A soundness test that passes both before
and after a change is not testing the change, and the only way to know which you
have is to check.

The unit tests cover a case `.sroof` syntax cannot express: a family with indices
but no parameters. `Bidirectional`'s check-mode route for constructors is guarded
on `params.nonEmpty`, so such a family goes through `inferCon` — a different
branch from the one the `.sroof` tests reach.

### Compatibility
Every new path is gated on a family both declaring indices *and* stating them on
every constructor. Every declaration that existed before this release — including
`stdlib/Vec.sroof` and `examples/vec.sroof`, which declare `(n: Nat)` but return a
bare `Vec` — fails that gate and takes the previous branch unchanged. The 590
pre-existing tests pass without modification, which here is a statement about the
gate rather than a coincidence.

### Not in this release
- **`checkMat` does not refine the expected type per branch.** This causes false
  negatives, not unsoundness: `checkCoverage` still requires a branch per
  constructor, and an unrefined return type is strictly harder to satisfy. It
  needs the same index abstraction as the tactic engine, so it moves to step 4.
- **Induction over an indexed family**, for the same reason. Proofs about
  concrete vectors work; proofs about all `Vec(A)(n)` do not.
- **`stdlib/Vec.sroof` still uses a phantom index.** Rewriting it now would give
  it a length it could state and not prove. See `docs/indexed-families.md`.

## [0.9.0] - 2026-08-07

Fixes the first of the two obstacles v0.8 identified under indexed families.

### Fixed
- **`IndChecker.instantiateArgType` indexed its arguments backwards.** Its own
  doc comment says `Var(0)` is the *most recent* previous constructor argument —
  which is what the elaborator produces, since it prepends each argument name to
  the scope — but the code read `prevArgs(abs)` while `checkArgsDependent` passes
  the arguments in **declaration order**. So `Var(0)` resolved to the *first*
  argument rather than the last.

  This was latent for as long as it was unreachable: a constructor argument type
  had to mention an earlier argument, and until v0.8 the parser could not express
  such a type. v0.8's multi-group application change made
  `case vcons(m: Nat, head: A, tail: Vec(A)(m))` writable, which reaches it
  directly — `tail`'s type would have been checked against `Vec A head` instead of
  `Vec A m`.

  All 590 tests pass unchanged, which is expected rather than reassuring: no
  existing declaration has a dependent constructor argument. A `.sroof` file that
  does is now checked correctly.

### Still outstanding
The second obstacle stands: `extractParamValsFromArgs` is a documented heuristic
("works for m=0 and simple m=1 cases") with no arguments to work from for a
nullary constructor. Indexed families step 3 — making `inferCon` apply
`retIndices` — needs that settled first. See `docs/indexed-families.md`.

## [0.8.0] - 2026-08-07

Groundwork for the two items v0.7 left outstanding: publishing is ready but for
credentials, and indexed families now parse and are recorded.

### Added — indexed families, steps 1 and 2
- **A constructor's return type may carry index arguments.**
  `case vnil: Vec(A)(Nat.zero)` was a parse error until now: `typeVarOrApp`
  accepted exactly one application group. It accepts any number and flattens
  them, so `Vec(A)(n)` and `Vec(A, n)` denote the same applied type — which
  arguments are parameters and which are indices is decided by the declaration,
  not by where the parentheses fall.
- **`CtorDef.retIndices` is populated.** It was a field nothing wrote. The
  elaborator now fills it from the declared return type, in the scope the last
  argument type sees, so an index may mention the constructor's own arguments.

  Both are backward compatible: a return type that is not an application of the
  inductive being declared, or that has the wrong argument count, yields `Nil` —
  exactly the previous behaviour. Every existing declaration means what it meant,
  and all 590 tests pass unchanged.

  **Indices still carry no information.** Steps 1 and 2 record them; the checker
  does not yet read them. `Vec.nil` and `Vec.cons(...)` still have the same type.
  See below.

### Attempted and reverted — indexed families, step 3
`IndChecker.inferCon` was extended to apply a constructor's `retIndices`, which
is what would finally make an index real. It passed all 590 tests — the change is
inert while `retIndices` is empty, which it is everywhere today — but
`#check Vec.vcons(...)` failed with `Unbound De Bruijn index 2`.

It was reverted rather than shipped. `inferCon` is inside the TCB for logical
validity, and an unvalidated change there is exactly what this project has
declined to ship in v0.5 and v0.6. `docs/indexed-families.md` records the two
obstacles the attempt uncovered — parameter inference is a documented heuristic
with nothing to work from for a nullary constructor, and `instantiateArgType`'s
ordering doc disagrees with its call site — so the next attempt starts informed.

### Added — publishing
- **Maven Central publishing is configured.** POM metadata (licence, SCM,
  developers, homepage — all of which Central rejects an artifact for missing),
  Sonatype wiring, `sbt-sonatype` and `sbt-pgp`, credentials read from the
  environment for CI, and a `ci-release-sroof` alias. `docs/publishing.md` says
  what to obtain and where to put it; `.github/workflows/release.yml` releases on
  a pushed `v*` tag and skips green when the secrets are absent, so an
  unconfigured repository or a fork is unaffected.

  Verified by `publishLocal`: `sroof-scala-api`, `sroof-scala-frontend`, and
  `sroof-scala-plugin` produce jar, sources, javadoc, and pom. Only credentials
  are missing.

  The groupId is `io.github.kmizu`, which Central verifies via the GitHub account
  of the same name. `io.sroof` would additionally need DNS verification of
  `sroof.io`; it is one value in `build.sbt`, and nothing is published yet, so
  switching costs nothing today.

### Documented
- **Indexed families are not implemented, contrary to appearances.**
  `docs/indexed-families.md` records the investigation. `IndDef.indices` is
  populated, but `CtorDef.retIndices` is a field **nothing writes or reads**, and
  a constructor's declared return type is parsed and discarded (`SCtor.retTpe`
  has no readers anywhere). The parser cannot even express
  `case vnil: Vec(A)(Nat.zero)`.

  So `stdlib/Vec.sroof` writing the bare `Vec` is not a convention to follow —
  it is the only thing that parses, and the `n: Nat` index is phantom:
  `Vec.nil` and `Vec.cons(...)` have the same type, and nothing about lengths can
  be stated. The file now says so.

  v0.7's fix does not extend to this. A type parameter has the same value in
  every constructor, so one uniform substitution sufficed; an index differs per
  constructor, so the motive must abstract over it and each branch must
  specialise it. The work starts in the parser and runs through the elaborator,
  checker, and tactic engine before any frontend work is meaningful.

## [0.7.0] - 2026-08-06

Lifts the limitation that had been recorded in `stdlib/PolyList.sroof` since the
polymorphic list was written: **induction over parameterised inductive types**.
That fix lives in the shared tactic engine, so it lands on both frontends at
once, and it is what made generic enums possible in the Scala path.

### Fixed (tactic engine, benefits both frontends)
- **Induction over a parameterised inductive.** `Builtins.buildFixCase` extended
  a branch's context with the constructor's **raw** argument types, which still
  mention the inductive's type parameters — indices that are bound nowhere in a
  branch context and silently pointed at `_rec` and `_n` instead. The scrutinee's
  type arguments are now substituted in first.
- **The branch context was based on the wrong context.** It dropped the induction
  variable while the proof term is placed in the goal's context. Those agree only
  when every entry a branch mentions is *newer* than the induction variable —
  true for the common shapes, which is why it went unnoticed, and false as soon
  as a type parameter is declared before the value being inducted on. Both are
  now stated in the goal's context.
- `Fix`'s body embeds the scrutinee's type inside its own binder, so that type
  needs shifting. It is the identity for a monomorphic (closed) type, which hid
  the problem.

### Added
- **Generic enums in the Scala frontend.** `enum Lst[A]`, definitions and
  theorems with type parameters, and induction over them:
  ```scala
  @theorem
  def appendAssoc[A](xs: Lst[A], ys: Lst[A], zs: Lst[A]): Proof =
    prove(append(append(xs, ys), zs) === append(xs, append(ys, zs)))(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      })
  ```
- **Worked examples of elementary mathematics.** `examples-scala3/Arithmetic.scala`
  proves the Peano addition and multiplication laws — the defining equations,
  their mirrors, and associativity — in the order a textbook would build them.
  `examples-scala3/Lists.scala` proves the list laws over a generic list,
  including that `length` distributes over `append`. Both are compiled with the
  plugin, so they are checked, not illustrative.
- `stdlib/PolyList.sroof` gains the inductive proofs its header used to say were
  impossible, and the header now explains the convention that makes them work.

### Changed
- `IndChecker.instantiateCtorArgTpe` and `extractIndParams` are public, so the
  tactic engine can reuse the checker's definition of the constructor-argument
  convention instead of restating it.

### Unchanged
- The trusted kernel. Every proof, generic or not, still goes through
  `Kernel.verify`.


## [0.6.0] - 2026-08-06

Adds `have`, so a proof can be written in steps, and converts another batch of
documented-but-untested claims into tested ones.

### Added
- **`have(claim)(proof) { h => ... }`** — prove an intermediate equation, bind it
  as `h`, and continue with it in scope. The claim becomes a goal in its own
  right, so `have` cannot be used to assume something convenient: an unprovable
  claim fails the theorem.

### Tested, not merely claimed
Two new suites compile constructs that were reachable by reading the extractor
but exercised by nothing:

- **Branch reordering.** `Term.Mat` matches branches to constructors *by
  position*, so a wrong normalisation would have produced a proof about the wrong
  branches rather than a failure. Out-of-order `match` and `induction` branches
  are now pinned.
- Two `@proofModule` objects in one file, a failure in the second still failing
  the compilation, enums with more than two cases, transitive inlining across a
  chain of definitions, `simplify` citing several verified theorems at once, and
  deeply nested constructor expressions.

All passed, so this release found no new defects there — unlike v0.5, where the
same exercise uncovered two.

### Documented
- **A second blocker under generic enums.** v0.5 identified
  `Builtins.buildFixCase` as the obstacle. Attempting the fix and running an
  inductive proof over `PolyList` surfaced another one underneath: the *bare*
  `Ind("PolyList")` written in stdlib definition signatures does not match the
  *applied* `App(Ind("PolyList"), A)` that a constructor field carries.
  Instantiating argument types does not reconcile those. `docs/scala3-frontend.md`
  §11 now records the required order of work, and why steps 1–2 are shared-code
  changes deserving their own milestone rather than a corner of a mixed release.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.

## [0.5.0] - 2026-08-06

Adds generalized induction — the first release to increase what the Scala path
can *prove*, rather than only what it can parse — and turns several documented
claims into tested ones.

### Added
- **`inductionGeneralizing(x, y, ...)`** — induction whose hypothesis is
  universally quantified over the other named parameters. Needed whenever those
  parameters change as the recursion proceeds, since a hypothesis fixed at their
  original values says nothing about the recursive call.
- **`exactIh(k)(at...)`** — closes the goal with that hypothesis, instantiated at
  the given values. Its arguments are expressions, not just names, because the
  interesting instantiations are at changed values (`Succ(acc)`).
- **References to parameterless definitions.** `def two: Nat = ...` could be
  declared but not used: a nullary reference arrives with no enclosing `Apply`,
  and fell through to "neither a binder nor a constructor".

### Fixed
- A parameterless definition was `Fix`-wrapped like any other. A nullary `Fix`
  can never reduce — it only unfolds when applied — so wherever it was inlined it
  sat unevaluated, and the evaluator failed on it. Parameterless definitions now
  translate to their body directly, matching the legacy elaborator, and nullary
  self-recursion is rejected with a diagnostic rather than left dangling.
- `mentionsIh` did not count `exactIh` as a use of the hypothesis, which would
  have meant the branch never requested one.

### Changed
- The `ih` diagnostics are now produced in one place and shared by `ih` and
  `exactIh`, so the two cannot drift apart. Wording changed slightly.
- The generic-enum rejection now explains *why*, and
  `docs/scala3-frontend.md` §11 records the real blocker (see below).

### Documented
- **Generic enums are blocked below the frontend, not in it.** Earlier drafts
  implied the work was frontend-side. In fact the core already represents
  parameterised inductives; what fails is induction over them, because
  `Builtins.buildFixCase` extends a branch context with raw constructor argument
  types that still mention the type parameters. `stdlib/PolyList.sroof` records
  the same limitation on the `.sroof` side. Supporting generics in the frontend
  alone would give generic declarations with no way to prove anything inductive
  about them; the fix belongs in `Builtins` and benefits both frontends.

### Tested, not merely claimed
A new suite pins constructs the subset table asserted but nothing exercised:
inferred local `val` types, `new Ctor(...)`, enum cases with explicit `extends`,
matching on a call result, multi-field non-recursive constructors, all-wildcard
patterns, mutually referring enums, and parameterless definitions — the last of
which turned out to be broken.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.

## [0.4.0] - 2026-08-06

Widens the Scala subset the compiler plugin accepts, and tightens the parts that
were already there.

### Added
- **Curried parameter lists.** `def f(a: A)(b: B)` and `@theorem def t(a: A)(b: B)`
  are supported. Lists are flattened — core types are curried anyway — and call
  sites are checked against the flattened arity, so partial application is
  rejected rather than silently accepted.
- **Runs of local `val`s.** A verified definition may now open with several
  immutable bindings, each visible to the next, instead of exactly one.
- **Recursive fields after other fields.** An induction hypothesis is generated
  whenever a constructor's *last* field has the inductive's own type, so
  `Cons(tag: Tag, rest: Tagged)` now supports `ih(rest)`. Previously only
  single-field constructors qualified.
- **`cases(x) { ... }`** — constructor split with no induction hypothesis. `ih`
  inside it is rejected with a message pointing at `induction`.
- **`rewrite(equations*)`** — applies equations as directed rewrites, alongside
  `simplify`'s normalise-then-close.

### Fixed
- The induction hypothesis was located by taking the head of an unordered map of
  pattern binders. With single-field constructors that happened to be correct;
  with the multi-field constructors this release accepts, it would have bound the
  hypothesis to an arbitrary field. It is now looked up by binder identity
  against the constructor's last field.
- `ih` on an unnamed (`_`) recursive field reported "no recursive field"; it now
  asks for the field to be bound to a name.
- The diagnostic for an unsupported block still claimed only a single `val` was
  allowed.

### Changed
- `docs/scala3-frontend.md`, both READMEs, and the normative example reflect the
  wider subset. The example now also demonstrates `cases`, curried theorem
  parameters, and `@simp` feeding a bare `simplify()`.
- Future work now records *why* generic enums are deferred rather than merely
  that they are: they touch the trusted translation layer at several points at
  once, and belong in their own milestone with per-construct golden tests.

### Unchanged
- The trusted kernel, and the `.sroof` language path in its entirety.



## [0.3.0] - 2026-08-06

The release that changes what sroof *is*: a Scala 3 verification system with an
independent proof kernel, rather than a separate Scala-like language.

### Added
- **Scala 3 frontend.** Theorems can now be stated and proved in ordinary
  `.scala` files, verified during compilation by a standard Scala 3 compiler
  plugin. Five new modules: `scala-api`, `scala-frontend`, `scala-plugin`,
  `examples-scala3`, `scala-it`.
- `sroof.annotation` markers (`@proofModule`, `@theorem`, `@simp`) and the
  `sroof.lang` DSL (`===`, `prove`, `trivial`, `induction`, `ih`, `simplify`).
  All proof values erase to inert `Unit`; nothing runs at runtime.
- A dotc-independent resolved IR and a Scala-to-core translation layer, so the
  translation, proof, and kernel layers stay portable across compiler versions.
- `docs/scala3-frontend.md`: motivation, architecture, the exact supported and
  unsupported subsets, translation rules, and the migration plan.
- `Eq.mkPropType`, a single definition of the propositional-equality encoding
  used for goals.
- CI job `scala-frontend`: frontend tests, plugin-enabled example compilation,
  runtime tests, and integration tests that invoke `dotc` for real.

### Changed
- `docs/trust-model.md` now separates two claims: **core logical validity**
  (decided by the kernel, unchanged) and **Scala semantic correspondence** (the
  claim that the core model *is* the Scala program). The Scala-to-core bridge is
  inside the TCB for the second claim, and the document says so plainly.
- `README.md` / `README-ja.md`: added the Scala 3 path, and corrected the tactic
  reference to match the implementation.
- `sbt-sroof` is documented as legacy `.sroof` integration, with the design for a
  future compiler-plugin mode recorded but deliberately not implemented.

### Fixed
- The tactic reference listed `ring` and the alias `induct`, neither of which
  exists in the parser, and conflated `assumption` with `assume`. The tables now
  match the implementation and cover the full tactic set.
- Documentation gave the native binary as `sroof-cli-native-out`; the build
  produces `sroof-cli-native`.

### Unchanged
- The `.sroof` language, parser, elaborator, CLI, extractor, stdlib, examples,
  VS Code extension, sbt plugin, and Scala Native binary all behave exactly as in
  v0.2. This is a supported legacy path, not a deprecated one.
- **The trusted kernel is byte-for-byte unchanged**, and no kernel test was
  weakened.

### Known limitations
- The Scala 3 frontend supports a deliberately narrow subset: non-generic enums,
  single-parameter-list pure `def`s over them, structural self-recursion,
  exhaustive matches, immutable local `val`s, equality goals, and the tactics
  `trivial`, `induction`, `ih`, `simplify`. Everything else is rejected with a
  diagnostic rather than approximated.
- `ih` requires a constructor with exactly one field of its own inductive type,
  and a pattern binder may not be named `ih`.
- Lemma reuse on the Scala path is limited to theorems verified earlier in the
  same module; there is no cross-compilation-unit proof metadata yet.
- `sorry` remains available on the `.sroof` path as an explicit unsound
  placeholder. The Scala path has no equivalent and never had one.

## [0.2.0] - 2026-03-02

### Added
- Richer tactic and proof authoring support in examples (`nat`, `int`, `list`, `vec`).
- Proof-state S-expression output on proof failures for tooling/LLM consumption.
- JSON output mode for `check --json`.
- VS Code extension with syntax highlighting, snippets, hover docs, and outline support.
- Scala Native build + CI smoke-test workflow.

### Changed
- Updated release documentation and v0.2 release checklist.
- Refined `examples/vec.sroof` to satisfy structural recursion checks.

### Known limitations
- Some advanced recursive patterns still require argument ordering that is friendly to the structural termination checker.
- `sorry` remains available as an explicit unsound placeholder and should not be used in production proofs.

