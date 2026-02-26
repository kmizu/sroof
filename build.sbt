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

// Phase 1-3: JVM only. Scala Native cross-compilation added in Phase 4.

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
