# sbt-sproof

An sbt plugin for the [sproof](https://github.com/kmizu/sproof) theorem prover.

## Usage

Add to `project/plugins.sbt`:
```sbt
addSbtPlugin("io.sproof" % "sbt-sproof" % "0.1.0")
```

Enable in your `build.sbt`:
```sbt
enablePlugins(SproofPlugin)
```

## Tasks

| Task | Description |
|------|-------------|
| `sproofCheck` | Type-check all `.sproof` files in `src/main/sproof/` |
| `sproofExtract` | Extract proofs to Scala 3 source code (runs automatically before compile) |
| `sproofRepl` | Start the interactive proof REPL |

## Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `sproofSources` | `Seq(src/main/sproof)` | Source directories for `.sproof` files |
| `sproofOutput` | `target/src_managed/main/sproof` | Output directory for extracted Scala files |
| `sproofVersion` | `"0.1.0"` | Version of sproof to use |

## Example

Create `src/main/sproof/nat.sproof`:
```
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

defspec refl(n: Nat): n = n program = {
  by induction n {
    case zero => trivial
    case succ k => trivial
  }
}
```

Then run:
```
sbt sproofCheck    # Type-check all .sproof files
sbt sproofExtract  # Extract to Scala 3 source files
sbt compile        # Full build (sproofExtract runs automatically before compile)
sbt sproofRepl     # Start the interactive REPL
```

## Custom source directory

```sbt
// In your project's build.sbt:
enablePlugins(SproofPlugin)
sproofSources := Seq(baseDirectory.value / "proofs")
```

## Development

This plugin is part of the sproof project. To publish locally for testing:

```
cd sbt-sproof
sbt publishLocal
```

Then in your test project's `project/plugins.sbt`:
```sbt
addSbtPlugin("io.sproof" % "sbt-sproof" % "0.1.0")
```
