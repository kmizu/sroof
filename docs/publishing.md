# Publishing sroof to Maven Central

Everything in the build is ready. What is missing is **credentials**, which
cannot live in the repository. This document says exactly what to obtain and
where to put it.

Nothing has been published yet, so none of the choices below are locked in.

## What gets published

| Artifact | Why a user needs it |
|---|---|
| `sroof-scala-api` | The annotations and DSL. Compiled into verified code — the one dependency a user's build actually declares. |
| `sroof-scala-plugin` | The compiler plugin. Referenced from `scalacOptions`, not from `libraryDependencies`. |
| `sroof-scala-frontend` | The IR, translation, and proof runner. A transitive dependency of the plugin. |
| `sroof-core`, `sroof-eval`, `sroof-checker`, `sroof-tactic`, `sroof-kernel` | The shared core. Transitive dependencies, and independently useful to anyone building on the kernel. |
| `sroof-syntax`, `sroof-extract`, `sroof-cli` | The `.sroof` path. |

Not published: `examples-scala3` and `scala-it` (an example and a test harness),
and the Scala Native mirrors (they build the same sources).

## The groupId decision

`build.sbt` opens with:

```scala
val publishOrganization = "io.github.kmizu"
```

Maven Central requires proof that you control the namespace. `io.github.kmizu`
is verified by owning the GitHub account of the same name — no extra steps.
`io.sroof` would additionally require DNS verification of the `sroof.io` domain.

Change that one value if you get the domain. Since nothing is published yet,
there is no migration cost today; after the first release there would be.

Whatever it says is what users write:

```scala
libraryDependencies += "io.github.kmizu" %% "sroof-scala-api" % "0.7.0"
```

## What you need to obtain

### 1. A Sonatype account and namespace

1. Register at <https://central.sonatype.com/> (or the legacy
   <https://s01.oss.sonatype.org/>, which is what the build is configured for).
2. Claim the `io.github.kmizu` namespace. Verification is a one-off: Sonatype
   asks you to create a public GitHub repository with a given name.
3. Generate a **user token** (not your password) from the account page. You get
   a token name and a token password.

### 2. A GPG signing key

Maven Central rejects unsigned artifacts.

```bash
gpg --gen-key                                   # RSA 4096, no expiry is fine
gpg --list-keys --keyid-format LONG             # note the key id
gpg --keyserver keyserver.ubuntu.com --send-keys <KEY_ID>
```

The public key must be on a keyserver before the first release, or the staging
repository will fail validation.

## Where the credentials go

### Local releases

`~/.sbt/1.0/sonatype.sbt` — **outside the repository**, and never committed:

```scala
credentials += Credentials(
  "Sonatype Nexus Repository Manager",
  "s01.oss.sonatype.org",
  "<token name>",
  "<token password>",
)
```

The GPG key is picked up from your keyring by `sbt-pgp`. If it is
passphrase-protected, sbt will prompt.

### CI releases

`.github/workflows/release.yml` releases on a pushed `v*` tag. It needs four
repository secrets (Settings → Secrets and variables → Actions):

| Secret | Value |
|---|---|
| `SONATYPE_USERNAME` | the token *name* |
| `SONATYPE_PASSWORD` | the token *password* |
| `PGP_SECRET` | `gpg --armor --export-secret-keys <KEY_ID> \| base64 -w0` |
| `PGP_PASSPHRASE` | the key's passphrase (omit the secret entirely if there is none) |

The workflow does nothing until those exist, and it is not wired into the normal
CI run, so an unconfigured repository is unaffected.

## Releasing

```bash
# 1. Everything green first.  A release is not the place to discover a failure.
sbt clean test
sbt "cli/run check examples/nat.sroof"

# 2. Bump the version in build.sbt (three occurrences) and vscode-sroof, write
#    the release notes and checklist, commit.

# 3. Stage, close, and release in one step.
sbt publishSigned sonatypeBundleRelease
```

`sonatypeBundleRelease` closes the staging repository and promotes it. Artifacts
appear on Maven Central within about ten minutes, and on search indexes within a
few hours.

To rehearse without publishing anything:

```bash
sbt publishLocal        # to ~/.ivy2/local
sbt publishM2           # to ~/.m2/repository
```

## After the first release

Downstream projects can then replace the local-build wiring with:

```scala
libraryDependencies += "io.github.kmizu" %% "sroof-scala-api" % "0.7.0"

// The plugin is a compiler plugin, so it goes on scalacOptions rather than
// libraryDependencies.  `addCompilerPlugin` does not work for it: dotc needs the
// whole plugin classpath, not just one artifact.
```

That also unblocks the `sbt-sroof` compiler-plugin mode, which is designed but
deliberately unimplemented while the artifacts do not exist — see
[`sbt-sroof/README.md`](../sbt-sroof/README.md).

## What is deliberately not automated

The version bump and the release notes. Both are judgement calls: which digit
moves, and what the release actually claims. The checklists in
`RELEASE_CHECKLIST_v*.md` exist because those claims should be verified rather
than generated.
