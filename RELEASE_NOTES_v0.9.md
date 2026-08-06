# sroof v0.9 Release Notes

Release date: 2026-08-07

A one-line fix, and worth a release because of what made it reachable.

## `instantiateArgType` indexed its arguments backwards

`IndChecker.instantiateArgType` substitutes a constructor's earlier arguments
into a later argument's type. Its own doc comment states the convention
correctly — `Var(0)` is the **most recent** previous argument, which is what the
elaborator produces, since it prepends each argument name to the scope.

The code did not follow it. It read `prevArgs(abs)`, while `checkArgsDependent`
passes the arguments in **declaration order**. So `Var(0)` resolved to the
*first* argument rather than the last.

```scala
// before
else if abs < j then Subst.shift(depth, prevArgs(abs))
// after
else if abs < j then Subst.shift(depth, prevArgs(j - 1 - abs))
```

## Why it mattered now

The bug was unreachable for as long as no constructor argument type could mention
an earlier argument — and until v0.8 the parser could not express such a type at
all. v0.8's multi-group application change made this writable:

```scala
inductive Vec(A: Type)(n: Nat) {
  case vnil: Vec
  case vcons(m: Nat, head: A, tail: Vec(A)(m)): Vec
}
```

`tail`'s type mentions `m`, the first argument, from the third position. With the
old indexing it would have been checked against `Vec A head` instead of
`Vec A m` — a type error on a correct program, or the wrong type accepted on an
incorrect one.

This is the pattern from v0.7 again: a latent coordinate bug that a passing suite
says nothing about, because nothing in the suite reaches it. **All 590 tests pass
unchanged here too**, and that is expected rather than reassuring — no existing
declaration has a dependent constructor argument. The evidence that the fix works
is a `.sroof` file that does, which now checks `OK`.

## Still outstanding

The other obstacle v0.8 recorded stands: `extractParamValsFromArgs` is a
documented heuristic ("works for m=0 and simple m=1 cases") with no arguments to
work from for a nullary constructor like `vnil`. Indexed families step 3 —
making `inferCon` apply `retIndices`, so an index finally carries information —
needs that settled first, and it is inside the TCB for logical validity, so it
wants negative soundness tests of its own.

`docs/indexed-families.md` tracks the six steps; two are done, and one of the two
blockers on step 3 is now cleared.

## Migration notes (from v0.8)

Nothing breaks. All 590 tests pass unchanged. The fix is observable only to a
constructor whose argument type mentions an earlier argument — which no
declaration written before v0.8 could express.

## Release artifacts

- Source release tag: `v0.9.0`
- JVM build via sbt
- VS Code extension package built from `vscode-sroof/` (unchanged)

Publishing to Maven Central remains configured and blocked only on credentials;
see `docs/publishing.md`.

## Verification performed for this release

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 590 passed, 0 failed |
| A `.sroof` file with a dependent constructor argument (`tail: Vec(A)(m)`) | checks OK |
| `git diff --check` | clean |
