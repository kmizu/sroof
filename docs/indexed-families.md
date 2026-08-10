# Indexed families and GADTs

Status as of v0.15.0: **steps 1–5 are done.** `stdlib/Vec.sroof` carries its length
in the type. Only step 6 (the Scala frontend / GADTs) remains.

Status as of v0.13.0: **steps 1–4 are done.** You can declare `Vec(A)(n)`, use it
as a parameter type, have the checker reject `Vec.vnil` where a length-one vector
was required, and prove things about an arbitrary vector by `cases` *or* by
`induction` with a working induction hypothesis.

Step 5 is blocked, but no longer by anything on this list — see below.

Everything under "What was actually there" describes the pre-v0.10 state and is
kept because the field comments and the surrounding code still carry its
assumptions in places.

## What v0.10.0 changed

`IndChecker.inferConWithParams` used to end with:

```scala
paramVals.foldLeft(Term.Ind(indRef, Nil, Nil): Term)(Term.App.apply)
```

where `paramVals` came from `extractParamsFromExpected` — the *expected* type's
own argument spine. The constructor's inferred type was therefore the expected
type, and the caller's conversion check compared it with itself. This checked
successfully on every release up to and including v0.9:

```scala
defspec vnil_is_not_length_one: Vec(Nat)(Nat.succ(Nat.zero)) { Vec.vnil }
```

A length-zero vector passed as a length-one vector. It is now rejected:

```
expected: ((Vec Nat) (succ zero))
actual:   ((Vec Nat) zero)
```

The parameter half of the spine is still read off the expected type, exactly as
it is for `List` and `Sigma`. The index half is **derived** from the
constructor's declared `retIndices`. `cli/.../IndexedFamilySuite.scala` holds the
negative tests; each was verified to *fail* against the v0.9 tree, which is the
only way to know they exercise the change rather than restating it.

Two smaller things came with it:

- A constructor whose return index mentions one of the family's own index
  variables — `case anylen: Bad(A)(n)` — is rejected. Such a declaration would
  reintroduce exactly the vacuity above, since the derived index would be
  whatever the caller asked for.
- `Term.show` now prints a constructor's arguments. Without that, an index
  mismatch rendered as `expected: Vec Nat succ / actual: Vec Nat succ` and read
  like a checker bug.

### What v0.10.0 deliberately left out

`checkMat` did not refine the expected type per branch — a source of false
negatives rather than unsoundness. ✅ **Done in v0.12.0**; see step 4.

`stdlib/Vec.sroof` was **not** rewritten to use real indices, and still has not
been: without the induction hypothesis it could declare a length and prove
nothing recursive about it, which is a worse state to ship than a phantom index
that is honest about being one. `examples/vec_indexed.sroof` demonstrates the
feature instead.

## What was actually there (pre-v0.10)

### `IndDef.indices` — populated, but behaves like extra parameters

`inductive Vec(A: Type)(n: Nat)` parses: the second parameter list becomes
`IndDef.indices`, and `Elaborator.elabInductive` puts those names in scope when
elaborating constructor argument types.

That much works. What it gives you is a second group of names visible inside the
declaration — not an index that varies per constructor.

### `CtorDef.retIndices` — declared, never written, never read

```scala
case class CtorDef(
  name:       String,
  argTpes:    List[Term],
  retIndices: List[Term] = Nil,   // "the concrete index values in the
                                  //  constructor's return type"
)
```

The doc comment says `Vec.nil` has `retIndices = [Nat.zero]` and `Vec.cons` has
`[Nat.succ(m)]`. Nothing produces that. `Elaborator.elabInductive` ends with:

```scala
CtorDef(ctor.name, argTpes)      // retIndices defaults to Nil, always
```

A repository-wide search for `retIndices` finds three hits, all in
`GlobalEnv.scala`: two comment lines and the field declaration. No reader, no
writer.

### The constructor's return type is parsed and discarded

`SCtor(name, argParams, retTpe)` carries the declared return type, and
`Parser.ctorDecl` fills it in. A repository-wide search for `.retTpe` finds **no
uses at all**. The elaborator never looks at it.

So in

```scala
inductive Vec(A: Type)(n: Nat) {
  case nil: Vec
  case cons(m: Nat, head: A, tail: Vec(A)): Vec
}
```

the two `: Vec` annotations are syntax the parser accepts and throws away.

### The parser cannot express an index anyway

```
case vnil: Vec(A)(Nat.zero)
                  ^^^^
Expected ->, case, or }.
```

`ctorDecl` parses the return type with `typeExpr`, which handles one application
group. A second one is a parse error. So even if the elaborator wanted the
return type, today's syntax could not state it.

**This is why `stdlib/Vec.sroof` writes the bare `Vec` everywhere.** It is not a
style choice or a convention to follow, as v0.7's `PolyList` fix might suggest by
analogy — it is the only thing the parser accepts.

### Consequence

`Vec` today is a list with a **phantom** index: the `n` is a name in scope during
elaboration and carries no information afterwards. `Vec.nil` and
`Vec.cons(...)` have the same type as far as the checker is concerned. Nothing
about lengths can be stated, let alone proved.

## Why v0.7's fix does not extend to this

v0.7 made induction work over *parameterised* inductives. The essential property
there was that **a type parameter has the same value in every constructor**, so a
branch context could be fixed up by substituting the scrutinee's type arguments
once, uniformly.

An index is different in exactly the way that matters: **it takes a different
value in each constructor**. `Vec A zero` and `Vec A (succ m)` are different
types. The motive therefore has to abstract over the index, and each branch has
to specialise it:

```text
parameterised (v0.7):   Fix(_rec, Pi(_n, Vec A n, P(_n)), ...)
indexed (needed):       Fix(_rec, Pi(i, Nat, Pi(_n, Vec A i, P(i)(_n))), ...)
                        …with branch `nil`  specialising i := zero
                        …and  branch `cons` specialising i := succ(m)
```

The closest existing code is `Builtins.inductionWithIHGeneralized`, which already
wraps the `Fix` type in extra `Pi`s and specialises them per branch
(`gAbs`, `genSpecializeGoal`). That is the shape to copy — but it generalises
over *context variables*, whereas this must generalise over an index whose value
is dictated by each constructor's declaration.

## Order of work

Each step is useful on its own and testable before the next begins.

1. **Parser.** ✅ **Done in v0.8.** `typeVarOrApp` accepted exactly one
   application group, so `Vec(A)(Nat.zero)` was a parse error. It now accepts
   any number of groups and flattens them: `Vec(A)(n)` and `Vec(A, n)` denote the
   same applied type, and which arguments are parameters and which are indices is
   decided by the declaration rather than by where the parentheses fall.

2. **Elaborator.** ✅ **Done in v0.8.** `CtorDef.retIndices` is populated from the
   declared return type, elaborated in the scope the *last* argument type sees so
   it may mention the constructor's own arguments. A return type that is not an
   application of the inductive being declared, or that carries the wrong number
   of arguments, yields `Nil` — which is exactly the previous behaviour, so every
   declaration written before this still means what it meant.

3. **Checker.** ✅ **Done in v0.10.0**, for constructors. `IndChecker` derives a
   constructor's index values from `retIndices` instead of echoing the expected
   type's spine — see "What v0.10.0 changed" above. `checkMat` still does not
   refine per branch; that moved to step 4, where it shares machinery with the
   tactic engine.

   What the v0.8 attempt got wrong, and what fixed it:

   - **Parameter inference is a heuristic**, and its window was the wrong width.
     `extractParamValsFromArgs` scanned `params.length` De Bruijn slots, but in
     an indexed family the indices sit *between* the constructor's arguments and
     the parameters. With a `p`-wide window the parameter vars fell past the end,
     hit the `else t` fallthrough, and reached `Eval` as free variables —
     `Unbound De Bruijn index 2 (env size 0)`. It now takes the width as a
     parameter: `p` for an ordinary inductive, `p + q` for an indexed one.
   - **No new traversal was needed.** `instantiateArgType` already decodes the
     elaborator's `(params ++ indices).reverse` layout, and `retIndices` is
     elaborated in the scope the last argument type sees. Instantiating it is the
     same call with `j = args.length` and the full `p + q` spine.
   - ~~**`instantiateArgType`'s ordering doc and its call site disagree.**~~
     ✅ **Fixed in v0.9.** The code read `prevArgs(abs)` while the call site
     passes declaration order, so `Var(0)` resolved to the first argument rather
     than the last. Reachable as of v0.8, which made
     `case vcons(m: Nat, head: A, tail: Vec(A)(m))` writable.

   This step is inside the TCB for logical validity, which is why every new path
   is gated on a family both declaring indices *and* stating them on every
   constructor. Anything else — including every declaration in the repository at
   the time — takes the pre-v0.10 branch unchanged.

4. **Tactic engine.** ✅ **Done — case analysis in v0.12.0, induction in v0.13.0.**

   **Case analysis refines the index.** Matching `vnil` out of a `Vec(A)(n)` now
   tells the branch that `n` is `Nat.zero`, so `cases` and `induction`-without-an-IH
   can prove things about an arbitrary vector:

   ```scala
   defspec vlen_matches_index(A: Type, n: Nat, v: Vec(A)(n)): vlen(A, n, v) = n {
     by cases v { case vnil => trivial  case vcons m h t => trivial }
   }
   ```

   The rule is the ordinary dependent-match one: within the branch for `c`, the
   scrutinee *is* `c(args)`, so the scrutinee's index and `c`'s declared index are
   the same thing. Refining is exactly abstracting the return type into a motive
   over the index and applying it at each constructor's index. It lives in
   `IndChecker.indexRefinement`, and both `checkCases` and `Builtins.specializeGoal`
   use it so the sub-goal a user is shown is the one the kernel will ask for.

   It fires only when the scrutinee's index argument is a plain **variable**.
   `v : Vec A (succ k)` refines nothing: concluding that `vnil` is unreachable, or
   that `succ k ≡ succ m` gives `k ≡ m`, needs real unification. Skipping leaves
   the branch at the unrefined type, which is strictly harder to prove.

   **`Bidirectional.infer` also had to learn the arity.** It folded `Ind` over
   parameters only, so `Vec(A)(n)` in a *binder* position failed with
   `Expected function type, got Type` — a theorem could state an index but no
   definition could take one as an argument. `Vec : Type → Nat → Type` now, gated
   on `isIndexed` so the phantom-index form keeps the shorter arity that
   `stdlib/Vec.sroof` is written against.

   **The induction hypothesis, added in v0.13.0.** `_rec` must accept the tail,
   whose index differs from the scrutinee's, so the `Fix` binds the index *before*
   the vector it describes:

   ```text
   Fix(_rec, Pi(_i, Nat, Pi(_n, Vec A _i, P(_i)(_n))),
     Lam(_i, Nat, Lam(_n, Vec A _i, Mat(Var(0), cases, P))))
     applied to (idx, scrutinee)
   ```

   Each branch specialises `_i` to that constructor's declared index, and the
   hypothesis is `_rec` applied to the *recursive argument's* index and the
   argument — which is what makes it usable. `Builtins.inductionIndexed`.

   `inductionWithIHGeneralized` was not reused: it binds `_n` outermost, so
   `varTpe`'s mention of the index would still point at the outer context.
   A separate path also leaves every existing induction shape literally untouched.

   **Everything is stated in `goal.ctx`**, never in a context with the scrutinee
   and index removed. The first attempt used `computeGeneralizedMotiveBody`, which
   removes its pivots, and the kernel rejected the result with
   `expected: Type, actual: ((Vec #3) #2)` — `A` is declared *before* both removed
   variables, which is precisely the case v0.7's coordinate rule 2 warns about.

   Fires only when the scrutinee's index argument is a plain context variable, the
   index type is closed, and there is exactly one index. Anything else takes the
   ordinary path unchanged. Two indices would need the Pi chain built in
   intermediate contexts, since the second index's type may mention the first.

   **What it looked like before v0.12** (measured in v0.11). Given

   ```scala
   def vlen(A: Type, n: Nat, v: Vec(A)(n)): Nat { ... }
   defspec vlen_correct(A: Type, n: Nat, v: Vec(A)(n)): vlen(A, n, v) = n {
     by induction v { case vnil => trivial  case vcons m h t ih => simplify [ih] }
   }
   ```

   the `vnil` branch produces

   ```
   (goal "((Eq ((((fix vlen) A) n) vnil)) n)")
   (error "trivial: not definitionally equal: ((((fix vlen) #4) #3) vnil) ≢ #3")
   ```

   The scrutinee was replaced by `vnil` but the **index was not**: the goal should
   be `vlen A zero vnil = zero`. That half is fixed; the `vlen` above is recursive,
   so it also needs the IH, which is the part that remains.

   Note that the proof state above is only legible because v0.11 fixed
   `ProofStatePretty.formatContext`; before that, `v` printed at type `Vec n v`.

5. **`.sroof` validation.** ✅ **Done in v0.15.0.** `stdlib/Vec.sroof` uses real
   indices, and `concat` carries the length theorem in its type:

   ```scala
   def concat(A: Type, n: Nat, m: Nat, xs: Vec(A)(n), ys: Vec(A)(m)): Vec(A)(plus(n, m))
   ```

   There is no separate lemma to prove — the return type *is* the statement, and
   since v0.14 a `def` body is kernel-checked, so it is verified rather than
   declared. `StdlibSuite` asserts that replacing it with `Vec(A)(Nat.zero)` makes
   the file stop checking, which is the only way to know the type is load-bearing.

   The file also proves `vlen_is_index` by induction, which needs the hypothesis at
   the tail's index — the v0.13 machinery, exercised on shipped code rather than on
   an example.

   The blocker was never the tactic engine in the end: it was that `def` bodies were
   not type-checked at all, so any length a definition declared was decoration.

6. **Scala frontend.** ⚠️ **Rejected rather than approximated, as of v0.16.**
   Scala has no indexed families; the equivalent is a GADT:

   ```scala
   enum Vec[A, N]:
     case VNil()                            extends Vec[A, Zero]
     case VCons[A, M](h: A, t: Vec[A, M])   extends Vec[A, Succ[M]]
   ```

   Until v0.16 such a declaration was **accepted with its index silently dropped**.
   `InductiveExtractor` instantiates every case's constructor at the enum's own
   type parameters — the thing that makes ordinary generic enums work — so both
   cases came out as constructors of a uniform `Vec[A, N]`.

   Not unsound: Scala's own typer still enforces the indices on the Scala side, and
   the core reading is the weaker parametric one, so the failure mode is a
   *rejected* proof rather than a false one. But the bridge's rule is to refuse
   what it cannot carry, precisely because nothing downstream can notice, and
   dropping an index is an approximation. It now refuses, naming the fixed
   argument.

   Supporting it needs a reading for a **type-level** index: Scala's `N` is a type
   where the core's is a value. `child.typeRef.baseType(enumClass).argInfos` gives
   the declared arguments — the extraction side is the easy half. Mapping a
   type-level `Nat` onto a core index is the design question, and it is the whole
   of the remaining work.

**Steps 1–5 are shared code that both frontends gain; step 6 is inside the
trusted Scala-to-core bridge.** As in v0.5–v0.7, the shared work goes first: a
frontend that extracts indices the core cannot check would produce declarations
nothing can be proved about, which is worse than a clean rejection.

## What is left

Steps 4–6. Step 4 is the delicate one and the one everything else waits on:
`Builtins.buildFixCase` has to abstract the motive over the index and specialise
it per branch, and the same abstraction is what lets `checkMat` refine the
expected type. Until it lands, an indexed family can be *stated* precisely but
only reasoned about at concrete indices — which is why `stdlib/Vec.sroof` stays
on the phantom form and step 5 has not started.

Steps 1–5 are shared code both frontends gain; step 6 is inside the trusted
Scala-to-core bridge and should not start before step 5 demonstrates that the
core supports what would be extracted *to*.

Each of these has been its own release. That pacing is deliberate: step 3 is
inside the TCB for logical validity, and the negative tests that justify it are
only meaningful if you can check them against the tree immediately before.
