val scala3Version = "3.3.6"

val commonSettings = Seq(
  scalaVersion := scala3Version,
  organization := "io.sproof",
  libraryDependencies ++= Seq(
    "org.typelevel" %% "cats-core" % "2.12.0",
    "org.scalameta" %% "munit"     % "1.0.2" % Test,
  ),
  testFrameworks += new TestFramework("munit.Framework"),
  scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
)

// Scala Native settings — used for the coreNative project.
// cats-core and munit both publish native artifacts.
val nativeSettings = Seq(
  scalaVersion := scala3Version,
  organization := "io.sproof",
  libraryDependencies ++= Seq(
    "org.typelevel" %%% "cats-core" % "2.12.0",
    "org.scalameta" %%% "munit"     % "1.0.2" % Test,
  ),
  testFrameworks += new TestFramework("munit.Framework"),
  scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
)

// ---- Root aggregate (JVM only — excludes Scala Native coreNative) ----
lazy val root = project.in(file("."))
  .aggregate(core, nbe, checker, tactic, syntax, extract, kernel, cli)
  .settings(
    name := "sproof",
    publish / skip := true,
  )

// ---- JVM projects (Phase 1-3) ----

lazy val core = project.in(file("core"))
  .settings(commonSettings)
  .settings(name := "sproof-core")

lazy val nbe = project.in(file("eval"))
  .dependsOn(core)
  .settings(commonSettings)
  .settings(name := "sproof-eval")

lazy val checker = project.in(file("checker"))
  .dependsOn(nbe)
  .settings(commonSettings)
  .settings(name := "sproof-checker")

lazy val tactic = project.in(file("tactic"))
  .dependsOn(checker)
  .settings(commonSettings)
  .settings(name := "sproof-tactic")

lazy val syntax = project.in(file("syntax"))
  .dependsOn(core)
  .settings(commonSettings)
  .settings(
    name := "sproof-syntax",
    libraryDependencies += "com.github.j-mie6" %% "parsley" % "5.0.0-M9",
  )

lazy val extract = project.in(file("extract"))
  .dependsOn(checker, tactic)  // tactic depends on checker which depends on nbe
  .settings(commonSettings)
  .settings(name := "sproof-extract")

lazy val kernel = project.in(file("kernel"))
  .dependsOn(checker, tactic)
  .settings(commonSettings)
  .settings(name := "sproof-kernel")

lazy val cli = project.in(file("cli"))
  .dependsOn(syntax, tactic, extract, kernel)
  .settings(commonSettings)
  .settings(
    name := "sproof-cli",
    Compile / mainClass := Some("sproof.Main"),
  )

// ---- Scala Native project (opt-in, Phase 4) ----
// coreNative compiles the trusted kernel (core module only) to native code.
// It shares sources with the JVM `core` project via `unmanagedSourceDirectories`.
// Dependencies: cats-core native, munit native (for tests).
//
// PREREQUISITES (Ubuntu/WSL2):
//   sudo apt-get install clang lld libunwind-dev
//
// Usage (must be explicit to avoid dependency resolution errors on systems without LLVM):
//   sbt coreNative/compile
//   sbt coreNative/test
//
// Excluded from the default aggregate (`aggregate in Global` / `sbt test`) so that
// the JVM build does not fail when LLVM is not installed.
lazy val coreNative = project.in(file("core-native"))
  .enablePlugins(ScalaNativePlugin)
  .settings(nativeSettings)
  .settings(
    name := "sproof-core-native",
    // Excluded from root aggregate: prevents "sbt test" from trying to resolve native deps
    aggregate := false,
    // Share sources with the JVM core project
    Compile / unmanagedSourceDirectories +=
      (core / Compile / sourceDirectory).value,
    Test / unmanagedSourceDirectories +=
      (core / Test / sourceDirectory).value,
  )
