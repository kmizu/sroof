# Release Checklist v0.5

Target release date: 2026-08-06

Every box marked `[x]` was actually executed and observed to pass. Boxes left
unchecked are genuinely outstanding and say why.

## Scope

- [x] Add `inductionGeneralizing` and `exactIh`, increasing what the Scala path
      can prove rather than only what it can parse.
- [x] Support references to parameterless definitions.
- [x] Turn documented-but-untested subset claims into tested ones.
- [x] Establish where the generic-enum blocker actually lives, and correct the
      documentation that implied it was frontend work.
- [x] Keep the architecture, the kernel, and the `.sroof` path untouched.

## Defects found and fixed

The first two were found by writing tests for claims the documentation already
made — which is the point of having written them.

- [x] A parameterless definition could be declared but not referenced: a nullary
      reference has no enclosing `Apply` to carry arguments.
- [x] Parameterless definitions were `Fix`-wrapped, and a nullary `Fix` never
      reduces, so it sat unevaluated wherever it was inlined. Now translated to
      the body directly, with nullary self-recursion rejected explicitly.
- [x] `mentionsIh` did not count `exactIh`, so a branch using it would not have
      requested a hypothesis at all.

## Honest testing

- [x] The generalized-induction example is pinned as provable **neither** by
      `trivial` nor by plain `induction`. An earlier candidate turned out to hold
      definitionally, which would have made the positive test vacuous; it was
      replaced rather than kept.
- [x] Each new capability is tested from both sides: what it accepts and the
      neighbouring case it must still refuse.

## Documentation and Versioning

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.5.md`).
- [x] Document generalized induction, including why `simplify` cannot consume a
      quantified hypothesis.
- [x] Rewrite the generic-enum entry in `docs/scala3-frontend.md` §11 with the
      real blocker, citing `Builtins.buildFixCase` and `stdlib/PolyList.sroof`.
- [x] Make the generic-enum rejection diagnostic explain why.
- [x] Update the Scala-path summary in `README.md` and `README-ja.md`.
- [x] Extend the normative example with generalized induction.
- [x] Bump sbt project version to `0.5.0`.
- [x] Bump VS Code extension version to `0.5.0`.

## Regression and Smoke Checks

- [x] `sbt clean test` — 571 passed, 0 failed (from a clean build)
- [x] `sbt "cli/run check examples/nat.sroof"` — OK
- [x] `sbt "cli/run check examples/int.sroof"` — OK
- [x] `sbt cliNative/compile`
- [x] `sbt cliNative/nativeLink`, then run the binary against `examples/nat.sroof` — OK
- [x] `cd sbt-sroof && sbt compile`
- [x] `cd vscode-sroof && npm ci && npm run compile`
- [x] `git diff --check` — clean

## Scala 3 frontend gates

- [x] `sbt scalaFrontend/test` — translation, golden core terms, proof runner.
- [x] `sbt scalaExamples/compile` — the extended example compiles with the plugin
      enabled, so every theorem in it passes the kernel.
- [x] `sbt scalaExamples/test` — the verified module still runs as an ordinary
      Scala program.
- [x] `sbt scalaIt/test` — 62 integration tests over real `dotc` invocations
      (47 in v0.4).

## Soundness review

- [x] Kernel source unchanged; no kernel test weakened.
- [x] Every accepted theorem still passes `Kernel.verify`. `exactIh` builds a
      candidate term like any other tactic; an instantiation that does not match
      the goal is rejected by the kernel, not by the frontend.
- [x] No new construct has more than one core reading.
- [x] No accepted translation produces an unresolved metavariable.
- [x] No catch-all branch was added: unrecognised trees still become positioned
      errors.

## Outstanding

- [ ] **Push the tags.** `v0.3.0`, `v0.4.0`, and `v0.5.0` exist locally on
      `release/v0.5.0`. Pushing them publishes the releases and was not
      authorised as part of preparing this one.
- [ ] **Publish `sroof-scala-api` and `sroof-scala-plugin`.** Still unpublished,
      so downstream projects must enable the plugin from a local build, and the
      `sbt-sroof` compiler-plugin mode stays designed-but-unimplemented.
- [ ] **Induction over parameterised inductives** in `Builtins` — the real
      prerequisite for generic enums, and a fix that would benefit the `.sroof`
      path too. See `docs/scala3-frontend.md` §11.
