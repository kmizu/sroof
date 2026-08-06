# Indexed families and GADTs

Status as of v0.10.0: **constructors are indexed; elimination is not.** You can
declare `Vec(A)(n)`, and the checker will reject `Vec.vnil` where a length-one
vector was required. You cannot yet prove anything by induction over such a
family. Steps 1–3 below are done; 4–6 are not.

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

### What is deliberately still missing

`checkMat` does not refine the expected type per branch. This is a source of
false negatives, not of unsoundness: `checkCoverage` still forces a branch for
every constructor, and an unrefined return type is strictly harder to satisfy.
It belongs with step 4, because the same index abstraction is what
`Builtins.buildFixCase` needs.

`stdlib/Vec.sroof` was **not** rewritten to use real indices. Without step 4 it
could declare a length and then prove nothing inductive about it, which is a
worse state to ship than a phantom index that is honest about being one.
`examples/vec_indexed.sroof` demonstrates the feature on concrete vectors
instead.

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

4. **Tactic engine.** `Builtins.buildFixCase` gains index abstraction and
   per-branch specialisation, mirroring `inductionWithIHGeneralized`.

   **What it looks like today** (measured in v0.11, so the next attempt starts
   from an observation rather than a guess). Given

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
   be `vlen A zero vnil = zero`. `n` is a context variable that the branch has to
   specialise, exactly as `specializeGoalOver` already specialises the scrutinee.
   `induction v generalizing n` does not help — generalising a context variable is
   not the same as tying it to the constructor's declared index.

   Note that the proof state above is only legible because v0.11 fixed
   `ProofStatePretty.formatContext`; before that, `v` printed at type `Vec n v`.

5. **`.sroof` validation.** Rewrite `stdlib/Vec.sroof` with real indices and
   prove something that needs them — `concat` preserving length is the obvious
   first target, and the file already defines `concat`.

6. **Scala frontend.** Scala has no indexed families; the equivalent is a GADT:

   ```scala
   enum Vec[A, N]:
     case VNil()                            extends Vec[A, Zero]
     case VCons[A, M](h: A, t: Vec[A, M])   extends Vec[A, Succ[M]]
   ```

   Extraction would read each case's `extends` arguments —
   `child.typeRef.baseType(enumClass).argInfos` — as its `retIndices`. How a
   type-level `Nat` maps onto a core index is a design question of its own, and
   should not be started before step 5 demonstrates the core actually supports
   what is being extracted *to*.

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
