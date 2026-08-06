# Release Checklist v0.6

Target release date: 2026-08-06

Every box marked `[x]` was actually executed and observed to pass. Boxes left
unchecked are genuinely outstanding and say why.

## Scope

- [x] Add `have`, so a proof can be written in steps rather than forced through
      a single tactic.
- [x] Convert another batch of documented-but-untested subset claims into tests.
- [x] Investigate the generic-enum blocker identified in v0.5, and report what
      the attempt found.
- [x] Keep the architecture, the kernel, and the `.sroof` path untouched.

## What the investigation found

- [x] Confirmed v0.5's diagnosis: `Builtins.buildFixCase` extends a branch
      context with raw constructor argument types that mention unbound type
      parameters.
- [x] Found a **second** blocker underneath it: stdlib definition signatures
      write the bare `Ind("PolyList")` while constructor fields carry the applied
      `App(Ind("PolyList"), A)`. Instantiating argument types does not reconcile
      them.
- [x] Recorded the required order of work in `docs/scala3-frontend.md` §11.
- [ ] **Not attempted further in this release.** Steps 1–2 are shared-code
      changes with 584 passing tests behind them and affect the `.sroof` path as
      much as the Scala one; they belong in their own milestone. A half-finished
      attempt was not shipped.

## Honest testing

- [x] Branch reordering is pinned. `Term.Mat` matches branches by position, so a
      wrong normalisation would yield a kernel-accepted proof about the wrong
      branches rather than a failure — the one case where a missing test could
      hide a real defect rather than merely a regression.
- [x] `have` is tested from both sides: it proves a real intermediate step, and
      an unprovable claim fails the theorem rather than being assumed.
- [x] All eight new module-shape tests passed on the first run. Unlike v0.5, this
      exercise found no new defects, and the release notes say so rather than
      implying otherwise.

## Documentation and Versioning

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.6.md`).
- [x] Document `have` in `docs/scala3-frontend.md`, including that its claim is
      checked rather than assumed.
- [x] Record the second generic-enum blocker and the resulting order of work.
- [x] Update the Scala-path summary in `README.md` and `README-ja.md`.
- [x] Extend the normative example with a stepwise `have` proof.
- [x] Bump sbt project version to `0.6.0`.
- [x] Bump VS Code extension version to `0.6.0`.

## Regression and Smoke Checks

- [x] `sbt clean test` — 584 passed, 0 failed (from a clean build)
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
- [x] `sbt scalaIt/test` — 75 integration tests over real `dotc` invocations
      (62 in v0.5).

## Soundness review

- [x] Kernel source unchanged; no kernel test weakened.
- [x] `have`'s intermediate claim is proved as a goal and bound by a `Let`; the
      whole term still goes through `Kernel.verify`.
- [x] No new construct has more than one core reading.
- [x] No catch-all branch was added.

## Outstanding

- [ ] **Push the tags.** `v0.3.0` through `v0.6.0` exist locally on
      `release/v0.6.0`. Pushing publishes the releases and was not authorised as
      part of preparing this one.
- [ ] **Publish `sroof-scala-api` and `sroof-scala-plugin`.**
- [ ] **Parameterised inductives**, in the order recorded in
      `docs/scala3-frontend.md` §11: settle the bare-vs-applied convention, then
      fix `Builtins.buildFixCase`, then add generic enums to the frontend.
