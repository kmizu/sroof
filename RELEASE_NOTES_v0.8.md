# sroof v0.8 Release Notes

Release date: 2026-08-07

Groundwork for the two items v0.7 left outstanding. Publishing is ready but for
credentials, and indexed families now parse and are recorded — though they still
do not *mean* anything, which this document is careful to be clear about.

## Publishing is configured

Maven Central rejects an artifact missing any of licence, SCM, developer, or
homepage, so the POM metadata is not decoration — a release fails without it.
That, the Sonatype wiring, `sbt-sonatype` and `sbt-pgp`, credentials read from
the environment so a CI release needs no on-disk secret, and a
`ci-release-sroof` alias are all in place.

Verified with `publishLocal`: `sroof-scala-api`, `sroof-scala-frontend`, and
`sroof-scala-plugin` each produce jar, sources, javadoc, and pom. **Only
credentials are missing.** `docs/publishing.md` says exactly what to obtain and
where to put it.

`.github/workflows/release.yml` releases on a pushed `v*` tag. It verifies the
tagged commit first, and skips green when the secrets are absent, so an
unconfigured repository or a fork is unaffected.

The groupId is `io.github.kmizu`, which Central verifies via the GitHub account
of the same name. `io.sroof` would additionally need DNS verification of
`sroof.io`. It is one value in `build.sbt`, and nothing is published yet, so
switching costs nothing today and would cost a migration later.

## Indexed families: two steps of six

v0.7's outstanding list said GADTs were the natural next step. Investigating
that turned up something worth stating plainly, because the source suggests the
opposite: **`CtorDef.retIndices` was a field nothing wrote or read**, and a
constructor's declared return type was parsed and discarded — `SCtor.retTpe` had
no readers anywhere. `stdlib/Vec.sroof` writing the bare `Vec` was not a
convention to follow by analogy with v0.7's `PolyList` fix; it was the only thing
that parsed.

Two of the six steps in `docs/indexed-families.md` are now done.

**Step 1, the parser.** `typeVarOrApp` accepted exactly one application group, so
`case vnil: Vec(A)(Nat.zero)` was a parse error. It now accepts any number and
flattens them: `Vec(A)(n)` and `Vec(A, n)` denote the same applied type, and
which arguments are parameters and which are indices is decided by the
declaration rather than by where the parentheses fall.

**Step 2, the elaborator.** `CtorDef.retIndices` is populated from the declared
return type, elaborated in the scope the last argument type sees so an index may
mention the constructor's own arguments — `Vec(A)(Nat.succ(m))` for
`case vcons(m: Nat, ...)`.

Both are backward compatible by construction. A return type that is not an
application of the inductive being declared, or that carries the wrong argument
count, yields `Nil` — exactly the previous behaviour. Every declaration written
before this means what it meant, and all 590 tests pass unchanged.

### What this does not yet do

**Indices still carry no information.** Steps 1 and 2 record them; nothing reads
them. `Vec.nil` and `Vec.cons(...)` still have the same type, and no proof can
mention a length. What you gain today is that the declaration can finally be
*written*.

## Step 3 was attempted and reverted

`IndChecker.inferCon` was extended to substitute a constructor's arguments and
parameters into its `retIndices` and apply the result — the change that would
finally make an index real.

It passed all 590 tests. That is less reassuring than it sounds: the change is
inert while `retIndices` is empty, which it is in every existing declaration. A
direct probe, `#check Vec.vcons(...)`, failed with
`Unbound De Bruijn index 2 (env size 0)`.

It was reverted rather than shipped. `inferCon` is inside the TCB for logical
validity, and shipping an unvalidated change there is what this project declined
to do in v0.5 and again in v0.6. A green suite that cannot see the new path is
not evidence about the new path.

The attempt was not wasted — it surfaced two obstacles the next one should start
from, both now recorded in `docs/indexed-families.md`:

- **Parameter inference is a documented heuristic.**
  `extractParamValsFromArgs` says it works "for m=0 and simple m=1 cases", and it
  has no arguments to work from at all for a nullary constructor like `vnil`. An
  index-aware `inferCon` cannot assume `paramVals` has the right length.
- **`instantiateArgType`'s ordering doc disagrees with its call site.** The
  comment says `Var(0)` is the *most recent* previous argument; `checkArgsDependent`
  passes `args.take(j)` in declaration order. This is latent today because few
  constructor argument types reference earlier arguments — but an index
  expression like `Nat.succ(m)` references them routinely, so it has to be
  settled before step 3 can be correct.

## Migration notes (from v0.7)

Nothing breaks. All 590 tests pass unchanged, and both `stdlib/Vec.sroof` and
`examples/vec.sroof` still check `OK`.

- The parser accepts strictly more than before.
- `CtorDef.retIndices` may now be non-empty for a declaration that states its
  indices. Nothing reads it, so this is observable only to code that inspects
  `IndDef` directly.

## Known limitations

Unchanged from v0.7, plus: indexed families parse but do not typecheck as
indexed. GADTs in the Scala frontend remain out of reach until steps 3–5 land in
the shared code — a frontend that extracted indices the core cannot check would
produce declarations nothing can be proved about.

## Release artifacts

- Source release tag: `v0.8.0`
- JVM build via sbt
- Scala Native binary from CI: `sroof-cli-linux-amd64`
- VS Code extension package built from `vscode-sroof/` (version `0.8.0`)

The compiler plugin is **configured for publishing but not yet published** — see
`docs/publishing.md`.

## Verification performed for this release

| Command | Result |
|---|---|
| `sbt clean test` (all modules, from scratch) | 590 passed, 0 failed |
| `sbt "cli/run check stdlib/Vec.sroof"` / `examples/vec.sroof` | OK |
| An indexed declaration (`case vnil: Vec(A)(Nat.zero)`) | parses and checks OK |
| `sbt scalaApi/publishLocal` and friends | jar, sources, javadoc, pom produced |
| `show ci-release-sroof` | alias registered |
| `git diff --check` | clean |
