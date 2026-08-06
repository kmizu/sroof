# Release Checklist v0.7

Target release date: 2026-08-06

Every box marked `[x]` was actually executed and observed to pass. Boxes left
unchecked are genuinely outstanding and say why.

## Scope

- [x] Fix induction over parameterised inductive types in the shared tactic
      engine — the item v0.5 identified and v0.6 deferred.
- [x] Add generic enums to the Scala frontend on top of that fix.
- [x] Lift the limitation `stdlib/PolyList.sroof` had carried, and add the proofs
      its header said were impossible.
- [x] Add worked examples of elementary mathematics, per user request, compiled
      with the plugin so they are checked rather than illustrative.
- [x] Keep the kernel untouched.

## Defects fixed in the tactic engine

All three shared one property: **each is the identity transformation on a
monomorphic type**, which is why 584 tests passed over them.

- [x] Branch contexts were extended with the constructor's *raw* argument types,
      whose `Var(j..j+m-1)` are the inductive's type parameters — bound nowhere in
      a branch context. Now instantiated at the scrutinee's type arguments.
- [x] The branch context was built by removing the induction variable, while the
      proof term is placed in the goal's context. Those agree only when every
      entry a branch mentions is newer than the induction variable. Both are now
      the goal's context.
- [x] `Fix`'s body embeds the scrutinee's type inside its own binder and was not
      shifted for it.

None could have produced an unsound proof — the kernel re-checks every term — so
the symptom was "cannot be proved", not "wrongly proved".

## Generic enums

- [x] Type parameters become leading `Type`-valued value parameters in core.
- [x] Call sites carry explicit type arguments recovered from the typed tree,
      since core does no inference.
- [x] Constructor field types are built with the *progressive* De Bruijn
      convention `IndChecker` defines, by hand, because it is the one place the
      frontend does not use ordinary innermost-first scoping.
- [x] A generic case's `PolyType` constructor is instantiated at the enum's own
      type parameters, which resolves the field types and lines each case's
      parameters up with the enum's positionally.
- [x] Tested from both sides: generic declarations, definitions, and inductive
      proofs are accepted; a false generic theorem is still rejected.

## Documentation

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.7.md`), including *why* the defects
      were invisible.
- [x] Rewrite the supported-subset and unsupported lists for generics.
- [x] Document the three coordinate conventions generics depend on.
- [x] Remove the now-obsolete Future Work entry for generic enums.
- [x] `stdlib/PolyList.sroof`: replace the "not supported" note with the
      convention that makes it work (declare the type parameter first).
- [x] Update the Scala-path summary in `README.md` and `README-ja.md`.
- [x] Bump sbt project version to `0.7.0`.
- [x] Bump VS Code extension version to `0.7.0`.

## Worked examples (user request)

- [x] `examples-scala3/Arithmetic.scala` — Peano addition and multiplication:
      the defining equations, their mirrors, associativity.
- [x] `examples-scala3/Lists.scala` — generic list laws: `append` unit laws,
      associativity, and `length` distributing over `append`.
- [x] Both compiled with the plugin enabled, so every theorem in them passes the
      kernel on every build.
- [x] Each theorem annotated with why it needs the tactic it uses, which is the
      part a subset table cannot convey.

## Regression and Smoke Checks

- [x] `sbt clean test` — 590 passed, 0 failed (from a clean build)
- [x] `sbt "cli/run check examples/nat.sroof"` — OK
- [x] `sbt "cli/run check examples/int.sroof"` — OK
- [x] `sbt "cli/run check stdlib/PolyList.sroof"` — OK, now including two
      inductive proofs over a polymorphic list
- [x] `sbt cliNative/compile`
- [x] `sbt cliNative/nativeLink`, then run the binary against `examples/nat.sroof` — OK
- [x] `cd sbt-sroof && sbt compile`
- [x] `cd vscode-sroof && npm ci && npm run compile`
- [x] `git diff --check` — clean

## Scala 3 frontend gates

- [x] `sbt scalaFrontend/test` — translation and proof runner.
- [x] `sbt scalaExamples/compile` — every theorem in the three example files
      passes the kernel.
- [x] `sbt scalaExamples/test` — the verified modules still run as ordinary
      Scala programs.
- [x] `sbt scalaIt/test` — 81 integration tests over real `dotc` invocations
      (75 in v0.6).

## Soundness review

- [x] Kernel source unchanged; no kernel test weakened.
- [x] The tactic-engine changes are outside the trust boundary: a wrong index
      yields a rejected proof, never an accepted falsehood.
- [x] The generics work *is* inside the Scala-to-core bridge, which is trusted
      for semantic correspondence. Each of the three conventions it relies on is
      documented at the point of use and covered by an end-to-end test that a
      false theorem in the same shape is rejected.
- [x] No catch-all branch was added.

## Outstanding

- [ ] **Push the tags.** `v0.3.0` through `v0.7.0` exist locally on
      `release/v0.7.0`. Pushing publishes the releases and was not authorised as
      part of preparing this one.
- [ ] **Publish `sroof-scala-api` and `sroof-scala-plugin`.**
- [ ] **GADTs and indexed families**, variance, and bounded type parameters —
      the natural next step now that plain parameterisation works.
