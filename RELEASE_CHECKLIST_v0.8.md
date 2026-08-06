# Release Checklist v0.8

Target release date: 2026-08-07

Every box marked `[x]` was actually executed and observed to pass. Boxes left
unchecked are genuinely outstanding and say why.

## Scope

- [x] Make publishing ready for credentials.
- [x] Land the first two steps of indexed families: a constructor's return type
      can carry indices, and they are recorded.
- [x] Report honestly that indices are recorded but not yet *read*.
- [x] Keep the kernel untouched.

## Publishing

- [x] POM metadata: licence, SCM, developers, homepage — Central rejects an
      artifact missing any of them.
- [x] `sbt-sonatype` and `sbt-pgp` added; the build still loads.
- [x] Credentials read from the environment, so a CI release needs no on-disk
      secret; local releases still use `~/.sbt/1.0/sonatype.sbt`.
- [x] `ci-release-sroof` alias registered (`show ci-release-sroof`).
- [x] `publishLocal` produces jar, sources, javadoc, and pom for
      `sroof-scala-api`, `sroof-scala-frontend`, and `sroof-scala-plugin`.
- [x] Publish/no-publish split verified: `core` and `cli` publish;
      `scalaIt` and `scalaExamples` do not.
- [x] `docs/publishing.md` covers what to obtain and where to put it, including
      why the groupId is `io.github.kmizu` rather than `io.sroof`.
- [x] `.github/workflows/release.yml` verifies the tagged commit, then skips
      green when the secrets are absent — a fork or unconfigured repository is
      unaffected.
- [ ] **Actually publish.** Blocked on a Sonatype account and a GPG key, neither
      of which can live in the repository.

## Indexed families

- [x] Step 1 — parser: a constructor's return type accepts several application
      groups, so `case vnil: Vec(A)(Nat.zero)` parses.
- [x] Step 2 — elaborator: `CtorDef.retIndices` is populated from that return
      type, in the scope the last argument type sees.
- [x] Backward compatible by construction: a return type that is not an
      application of the inductive being declared, or that has the wrong argument
      count, yields `Nil` — the previous behaviour.
- [x] Verified: an indexed declaration parses and checks `OK`; all 590 existing
      tests pass unchanged; `stdlib/Vec.sroof` and `examples/vec.sroof` still
      check `OK`.
- [ ] **Step 3 — checker. Attempted and reverted.** `inferCon` was extended to
      apply `retIndices`. It passed all 590 tests, which is weak evidence: the
      change is inert while `retIndices` is empty, which it is everywhere today.
      A direct probe (`#check Vec.vcons(...)`) failed with
      `Unbound De Bruijn index 2`. `inferCon` is inside the TCB for logical
      validity, so it was reverted rather than shipped.

      The two obstacles it uncovered are recorded in
      `docs/indexed-families.md`: parameter inference is a documented heuristic
      with nothing to work from for a nullary constructor, and
      `instantiateArgType`'s ordering doc disagrees with its call site.
- [ ] Steps 4–6 (tactic engine, `.sroof` validation, Scala frontend) — blocked
      on step 3.

## What this release does not claim

- [x] The release notes say plainly that indices carry no information yet, and
      that `Vec.nil` and `Vec.cons(...)` still have the same type. A reader
      should not come away thinking GADTs work.
- [x] The notes also say why 590 green tests were *not* enough to justify
      shipping step 3.

## Documentation and Versioning

- [x] Update root changelog (`CHANGELOG.md`).
- [x] Add release notes (`RELEASE_NOTES_v0.8.md`).
- [x] Mark steps 1–2 done and step 3 attempted-and-reverted in
      `docs/indexed-families.md`, with what the attempt learned.
- [x] Update `README.md`, `README-ja.md`, and the docs index.
- [x] Bump sbt project version to `0.8.0`.
- [x] Bump VS Code extension version to `0.8.0`.

## Regression and Smoke Checks

- [x] `sbt clean test` — 590 passed, 0 failed (from a clean build)
- [x] `sbt "cli/run check stdlib/Vec.sroof"` and `examples/vec.sroof` — OK
- [x] An indexed declaration parses and checks OK
- [x] `git diff --check` — clean

## Outstanding

- [ ] **Publish to Maven Central** — needs credentials; everything else is ready.
- [ ] **Indexed families step 3 onward** — start from the two obstacles recorded
      in `docs/indexed-families.md`, and give the checker change its own
      negative soundness tests.
