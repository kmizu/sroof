# Indexed families and GADTs — groundwork

Status: **not implemented.** This document records what is actually in the code
today, what is only declared, and the order the work has to happen in.

It exists because the obvious reading of the source is wrong in a way that would
cost someone a day: `IndDef.indices` and `CtorDef.retIndices` look like support
for indexed families, and one of them is a field nothing ever writes.

## What is actually there

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

3. **Checker.** ⚠️ **Attempted in v0.8 and reverted.** `IndChecker.inferCon` must
   produce the *applied* type `Vec A <retIndices>` rather than the bare head, and
   `checkMat` must refine the expected type per branch. Until this lands, indices
   still carry no information: steps 1 and 2 record them, and nothing reads them.

   The v0.8 attempt substituted the constructor's arguments and parameters into
   `retIndices` and applied the result. It passed all 590 existing tests — the
   change is inert when `retIndices` is empty, which it is everywhere today — but
   `#check Vec.vcons(...)` failed with `Unbound De Bruijn index 2 (env size 0)`.
   Two things to know before the next attempt:

   - **Parameter inference is a heuristic.** `extractParamValsFromArgs` is
     documented as working "for m=0 and simple m=1 cases", and it has no
     arguments to work from for a nullary constructor like `vnil`. An index-aware
     `inferCon` cannot assume `paramVals` has the right length.
   - ~~**`instantiateArgType`'s ordering doc and its call site disagree.**~~
     ✅ **Fixed in v0.9.** The code read `prevArgs(abs)` while the call site
     passes declaration order, so `Var(0)` resolved to the first argument rather
     than the last. Reachable as of v0.8, which made
     `case vcons(m: Nat, head: A, tail: Vec(A)(m))` writable.

   This step is inside the TCB for logical validity. It wants negative soundness
   tests of its own, and it should not be attempted as part of a release that is
   also doing other things.

4. **Tactic engine.** `Builtins.buildFixCase` gains index abstraction and
   per-branch specialisation, mirroring `inductionWithIHGeneralized`.

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

## Estimate

Larger than v0.7. That release fixed three coordinate bugs in existing
machinery; this one adds a concept the parser, elaborator, checker, and tactic
engine have never carried. Steps 1–2 are small; step 3 touches the checker, which
is inside the TCB for logical validity and therefore wants negative soundness
tests of its own; step 4 is the delicate De Bruijn work.

It should be its own milestone, and it should not be attempted alongside other
features.
