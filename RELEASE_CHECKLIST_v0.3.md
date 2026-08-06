# Release Checklist v0.3

Target release date: 2026-08-06

Every box marked `[x]` below was actually executed and observed to pass. Boxes
left unchecked are genuinely outstanding and say why.

## Documentation and Versioning

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.3.md`).
- [x] Add the Scala 3 frontend architecture document (`docs/scala3-frontend.md`).
- [x] Rewrite `docs/trust-model.md` to separate core logical validity from Scala
      semantic correspondence, and to name the new TCB members.
- [x] Add the Scala 3 path to `README.md` and `README-ja.md`, labelled as an
      initial subset.
- [x] Update release links and migration notes in `README.md` / `README-ja.md`.
- [x] Update contributor guidance (`AGENTS.md`, `CLAUDE.md`).
- [x] Document `sbt-sroof` as legacy integration and record the design for a
      future compiler-plugin mode.
- [x] Bump sbt project version to `0.3.0`.
- [x] Bump VS Code extension version to `0.3.0` (`package.json`,
      `package-lock.json`, `CHANGELOG.md`, install instructions).

## Documentation accuracy

Corrections found while preparing the release; each was verified against the
implementation before changing the docs.

- [x] Tactic reference listed `ring`, which no longer exists in the parser.
- [x] Tactic reference listed the alias `induct`, which does not exist.
- [x] Tactic reference conflated `assumption` (closes a goal from context) with
      `assume` (introduces a binder). They are separate tactics.
- [x] Tactic reference omitted roughly half the implemented tactics; both
      READMEs now cover the full set, including combinators and simp modifiers.
- [x] Native binary documented as `sroof-cli-native-out`; the build produces
      `sroof-cli-native`.
- [x] Both READMEs declared an MIT licence and linked to a `LICENSE` file that
      did not exist. Added the MIT text, making the already-stated licence
      concrete. **The copyright line reads `2026 Kota Mizushima`, taken from the
      repository's commit history — a maintainer should confirm it.**

## Regression and Smoke Checks

- [x] `sbt kernel/test` — 14 passed
- [x] `sbt clean test` — 539 passed, 0 failed (from a clean build)
- [x] `sbt "cli/run check examples/nat.sroof"` — OK
- [x] `sbt "cli/run check examples/int.sroof"` — OK
- [x] `sbt cliNative/compile`
- [x] `sbt cliNative/nativeLink`, then run the binary against `examples/nat.sroof` — OK
- [x] `cd sbt-sroof && sbt compile`
- [x] `cd vscode-sroof && npm ci && npm run compile`
- [x] `git diff --check` — clean

## Scala 3 frontend gates

- [x] `sbt scalaFrontend/test` — translation, golden core terms, differential
      check against Scala evaluation, proof runner, kernel gate.
- [x] `sbt scalaExamples/compile` — the normative example compiles with the
      plugin enabled, so all four Nat theorems pass the kernel.
- [x] `sbt scalaExamples/test` — the verified module still runs as an ordinary
      Scala program.
- [x] `sbt scalaIt/test` — 32 integration tests over real `dotc` invocations.
- [x] Confirmed empirically that the plugin is actually running: a deliberately
      false theorem fails compilation with a positioned `[sroof]` error. A plugin
      that silently did nothing would otherwise be indistinguishable from success.

## Soundness review

- [x] Every accepted theorem on both paths passes `Kernel.verify`.
- [x] Kernel source unchanged; no kernel test weakened or removed.
- [x] No `sorry`, warning-only mode, or fallback proof exists on the Scala path.
- [x] No accepted Scala translation contains an unresolved metavariable
      (asserted by test, not by inspection).
- [x] Negative tests cover false proofs, invalid `ih`, wrong theorem shape,
      theorems outside `@proofModule`, wrong result type, missing and duplicate
      induction branches.
- [x] Negative tests cover unsupported computation: `var`, assignment, external
      effects, non-structural recursion, mutual recursion, external calls,
      unsupported types, classes, generic enums, guards, lambdas.
- [x] Symbol-identity tests prove a user-defined `prove` / `trivial` / `simplify`
      / `===` is never mistaken for the DSL.

## CI and Artifacts

- [x] CI includes the kernel soundness gate, JVM tests, benchmarks, native
      build, and the sbt plugin.
- [x] CI includes the new `scala-frontend` job covering frontend tests,
      plugin-enabled compilation, runtime tests, and integration tests.
- [x] Confirm native binary artifact name/path (`sroof-cli-linux-amd64`).

## Outstanding

- [ ] **Tag and publish.** Creating the `v0.3.0` tag and pushing artifacts is
      left to a maintainer: it is outward-facing and was not authorised as part
      of preparing this release.
- [ ] **Publish `sroof-scala-api` and `sroof-scala-plugin`.** Until these are in
      a repository, downstream projects must enable the plugin from a local
      build. The `sbt-sroof` compiler-plugin mode is blocked on this and is
      documented as designed-but-unimplemented rather than stubbed.
