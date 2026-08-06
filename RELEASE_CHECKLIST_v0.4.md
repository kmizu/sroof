# Release Checklist v0.4

Target release date: 2026-08-06

Every box marked `[x]` was actually executed and observed to pass. Boxes left
unchecked are genuinely outstanding and say why.

## Scope

- [x] Widen the accepted Scala subset: curried parameter lists, runs of local
      `val`s, recursive constructor fields that follow other fields.
- [x] Add the `cases` and `rewrite` tactics to the DSL.
- [x] Fix the defects the widening exposed (see below).
- [x] Keep the architecture, the kernel, and the `.sroof` path untouched.

## Defects fixed

- [x] The induction hypothesis was located via `Map.keys.headOption` — an
      unordered lookup that was only accidentally correct for single-field
      constructors, and would have bound the hypothesis to an arbitrary field
      once multi-field constructors were accepted. Now looked up by binder
      identity against the constructor's last field, with a test that a
      non-final field is rejected.
- [x] `ih` on an unnamed (`_`) recursive field gave a misleading "no recursive
      field" message.
- [x] The unsupported-block diagnostic still said only one `val` was allowed.

## Documentation and Versioning

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.4.md`).
- [x] Update the supported/unsupported subset in `docs/scala3-frontend.md`.
- [x] Record *why* generic enums are deferred, not just that they are.
- [x] Update the Scala-path summary in `README.md` and `README-ja.md`.
- [x] Extend the normative example to exercise `cases`, curried theorem
      parameters, and `@simp` feeding a bare `simplify()`.
- [x] Bump sbt project version to `0.4.0`.
- [x] Bump VS Code extension version to `0.4.0`.

## Regression and Smoke Checks

- [x] `sbt clean test` — 556 passed, 0 failed (from a clean build)
- [x] `sbt "cli/run check examples/nat.sroof"` — OK
- [x] `sbt "cli/run check examples/int.sroof"` — OK
- [x] `sbt cliNative/compile`
- [x] `sbt cliNative/nativeLink`, then run the binary against `examples/nat.sroof` — OK
- [x] `cd sbt-sroof && sbt compile`
- [x] `cd vscode-sroof && npm ci && npm run compile`
- [x] `git diff --check` — clean

## Scala 3 frontend gates

- [x] `sbt scalaFrontend/test` — 14 passed, including golden `Cases` and
      `Rewrite` coverage at the layer below the compiler.
- [x] `sbt scalaExamples/compile` — the extended example compiles with the plugin
      enabled, so all seven theorems pass the kernel.
- [x] `sbt scalaExamples/test` — the verified module still runs as an ordinary
      Scala program.
- [x] `sbt scalaIt/test` — 47 integration tests over real `dotc` invocations
      (32 in v0.3).

## Widening tested from both sides

Each new capability has a test for what it accepts *and* for the neighbouring
case it must still refuse.

- [x] Curried lists accepted / partial application rejected.
- [x] Runs of `val`s accepted / a `var` among them rejected.
- [x] Recursive last field accepted / `ih` on a non-final field rejected /
      `ih` on an unnamed field rejected.
- [x] `cases` accepted / `ih` inside `cases` rejected / missing branch rejected.
- [x] `rewrite` closes a true goal / does not rescue a false one.
- [x] Bare `simplify()` draws on the `@simp` set.

## Soundness review

- [x] Kernel source unchanged; no kernel test weakened.
- [x] Every accepted theorem still passes `Kernel.verify`.
- [x] No new construct has more than one core reading; each is pinned by a test.
- [x] No accepted translation produces an unresolved metavariable.
- [x] The widening added no catch-all branch: every unrecognised tree still
      becomes a positioned error.

## Outstanding

- [ ] **Tag and publish.** Creating the `v0.4.0` tag and pushing artifacts is
      left to a maintainer: it is outward-facing and was not authorised as part
      of preparing this release.
- [ ] **Publish `sroof-scala-api` and `sroof-scala-plugin`.** Still unpublished,
      so downstream projects must enable the plugin from a local build, and the
      `sbt-sroof` compiler-plugin mode stays designed-but-unimplemented.
- [ ] **Generic enums.** Deliberately deferred to their own milestone; see
      `docs/scala3-frontend.md` §11 for the reasoning.
