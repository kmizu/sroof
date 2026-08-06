# sbt-sroof

An sbt plugin for the [sroof](https://github.com/kmizu/sroof) theorem prover.

Automatically type-checks `.sroof` files and extracts verified Scala 3 source code as part of your sbt build.

> **Status: legacy integration.** This plugin drives the `.sroof` language and its
> extraction workflow. It is fully supported and unchanged, but it is not the
> direction sroof is heading: the newer Scala 3 frontend verifies ordinary
> `.scala` sources in place, so there is nothing to extract. See
> [Future: compiler-plugin mode](#future-compiler-plugin-mode).

---

## Setup

### 1. Add the plugin

In `project/plugins.sbt`:

```sbt
addSbtPlugin("io.sroof" % "sbt-sroof" % "0.1.0")
```

### 2. Enable in your build

In `build.sbt`:

```sbt
enablePlugins(SroofPlugin)
```

### 3. Install the sroof CLI

Either put `sroof` on your `PATH`:

```bash
# Download the sroof CLI uber-JAR and create a wrapper script, or
# build from source:
git clone https://github.com/kmizu/sroof && cd sroof
sbt cli/assembly   # produces cli/target/scala-3.x.x/sroof-cli-assembly-*.jar
```

Or configure the plugin to use a specific JAR:

```sbt
// build.sbt
enablePlugins(SroofPlugin)
sroofJar := Some(file("/path/to/sroof-cli-assembly.jar"))
```

---

## Tasks

| Task           | Description                                                        |
|----------------|--------------------------------------------------------------------|
| `sroofCheck`  | Type-check all `.sroof` files in `sroofSources`                  |
| `sroofExtract`| Extract proofs to Scala 3 (runs automatically before `compile`)    |
| `sroofRepl`   | Start the interactive sroof REPL                                  |

```bash
sbt sroofCheck    # check all .sroof files
sbt sroofExtract  # extract to target/src_managed/main/sroof/
sbt sroofRepl     # interactive REPL
sbt compile        # sroofExtract runs automatically before Scala compilation
```

---

## Settings

| Setting         | Type              | Default                            | Description                                         |
|-----------------|-------------------|------------------------------------|-----------------------------------------------------|
| `sroofVersion` | `String`          | `"0.1.0"`                          | Version of sroof to use                            |
| `sroofSources` | `Seq[File]`       | `Seq(src/main/sroof)`             | Directories containing `.sroof` files              |
| `sroofOutput`  | `File`            | `target/src_managed/main/sroof`   | Output directory for generated Scala files          |
| `sroofJar`     | `Option[File]`    | `None` (use `sroof` on PATH)      | Path to the sroof CLI uber-JAR                     |
| `sroofJvmOpts` | `Seq[String]`     | `Seq("-Xss8m")`                    | JVM options when forking the sroof process         |

---

## Example

### Project layout

```
my-project/
├── project/
│   └── plugins.sbt            # addSbtPlugin("io.sroof" % "sbt-sroof" % "0.1.0")
├── src/
│   └── main/
│       ├── scala/
│       │   └── Main.scala
│       └── sroof/
│           └── nat.sroof     # your proof file
└── build.sbt
```

### `src/main/sroof/nat.sroof`

```scala
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n program = {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

### `build.sbt`

```sbt
scalaVersion := "3.3.6"
enablePlugins(SroofPlugin)

// Optional: custom source directory
// sroofSources := Seq(baseDirectory.value / "proofs")

// Optional: use a specific JAR instead of PATH
// sroofJar := Some(file("/path/to/sroof-cli-assembly.jar"))
```

### Running

```bash
$ sbt sroofCheck
[info] sroof: Checking 1 file(s)...
[info]   OK: src/main/sroof/nat.sroof — 1 inductive(s), 1 definition(s), 1 defspec(s)
[success] sroof: All 1 file(s) passed.

$ sbt compile        # also runs sroofExtract automatically
[info] sroof: Extracting nat.sroof → nat.scala
[info] compiling 2 Scala sources ...
```

---

## Custom source directory

```sbt
enablePlugins(SroofPlugin)
sroofSources := Seq(baseDirectory.value / "proofs")
```

---

## Incremental extraction

`sroofExtract` skips files that haven't changed since the last extraction (source `.lastModified` vs generated file). The generated files are placed in `target/src_managed/main/sroof/` and automatically added to the Scala compilation classpath.

---

## Future: compiler-plugin mode

The Scala 3 frontend verifies `.scala` sources in place, so there is nothing to
extract and no CLI to shell out to. A future mode of this plugin would replace
the extraction workflow with two build edits:

```sbt
// sketch — not implemented
libraryDependencies += "io.sroof" %% "sroof-scala-api"    % sroofVersion
Compile / scalacOptions += "-Xplugin:" + sroofPluginClasspath.value
```

where `sroofPluginClasspath` resolves `sroof-scala-plugin` and its runtime
dependencies, with the plugin JAR first (it carries `plugin.properties`).

**This mode is deliberately not implemented yet.** Wiring it up would mean
depending on `io.sroof` artifacts that are not published, so the plugin would
either fail at resolution or need a fake local path — and a half-working
packaging story is worse than an honest note. The design is recorded here and in
[`docs/scala3-frontend.md`](../docs/scala3-frontend.md); implementation waits on
publication.

Nothing about the current `.sroof` extraction behaviour changes in the meantime.

---

## Development

To test the plugin locally:

```bash
cd sbt-sroof
sbt publishLocal
```

Then in your test project's `project/plugins.sbt`:

```sbt
addSbtPlugin("io.sroof" % "sbt-sroof" % "0.1.0")
```
