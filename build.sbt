import scala.scalanative.build._

// ---- Publishing coordinates ----
//
// Maven Central requires you to prove you control the groupId's namespace.
// `io.github.kmizu` is verified by owning the GitHub account of the same name,
// so it works today with no extra steps.  `io.sroof` would additionally require
// DNS verification of `sroof.io`; switch this one value once that is in place —
// nothing has been published yet, so the coordinates are still free to choose.
//
// Whatever this says is what users will write:
//   libraryDependencies += "io.github.kmizu" %% "sroof-scala-api" % "0.19.0"
val publishOrganization = "io.github.kmizu"

val scala3Version  = "3.3.6"
val parsleyVersion = "5.0.0-M19"  // JVM + Native 共通（M15+ が native 対応）
val catsVersion    = "2.12.0"
val munitVersion   = "1.0.2"

// ---- Shared settings ----

val commonSettings = Seq(
  scalaVersion := scala3Version,
  version := "0.37.0",
  organization := "io.sroof",
  libraryDependencies ++= Seq(
    "org.typelevel" %% "cats-core" % catsVersion,
    "org.scalameta" %% "munit"     % munitVersion % Test,
  ),
  testFrameworks += new TestFramework("munit.Framework"),
  scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
)

/** POM metadata and Sonatype wiring, applied to every module that ships.
 *
 *  Maven Central rejects an artifact missing any of licence, SCM, developer, or
 *  homepage, so these are not decoration — a release fails without them.
 *
 *  Publishing additionally needs two secrets that are deliberately *not* in this
 *  file: a Sonatype token and a GPG signing key.  See `docs/publishing.md`.
 */
val publishSettings = Seq(
  organization         := publishOrganization,
  organizationName     := "sroof",
  organizationHomepage := Some(url("https://github.com/kmizu/sroof")),
  homepage             := Some(url("https://github.com/kmizu/sroof")),
  licenses             := Seq("MIT" -> url("https://opensource.org/licenses/MIT")),
  scmInfo := Some(ScmInfo(
    url("https://github.com/kmizu/sroof"),
    "scm:git:https://github.com/kmizu/sroof.git",
    Some("scm:git:git@github.com:kmizu/sroof.git"),
  )),
  developers := List(Developer(
    id    = "kmizu",
    name  = "Kota Mizushima",
    email = "kmizu.main@gmail.com",
    url   = url("https://github.com/kmizu"),
  )),
  // Tells downstream tooling that 0.x versions may break compatibility.
  versionScheme := Some("early-semver"),
  publishMavenStyle := true,
  publishTo := sonatypePublishToBundle.value,
  sonatypeCredentialHost := "s01.oss.sonatype.org",
  Test / publishArtifact := false,
  pomIncludeRepository := { _ => false },
)

/** For modules that exist only to build or test the others. */
val noPublishSettings = Seq(
  publish / skip := true,
  publishArtifact := false,
)

// Sonatype credentials come from the environment in CI and from
// ~/.sbt/1.0/sonatype.sbt locally.  Reading them here rather than requiring the
// file means a CI release needs no on-disk secret.
// (build.sbt is compiled as Scala 2.12, so no brace-less `match` here.)
ThisBuild / credentials ++= {
  val user = sys.env.get("SONATYPE_USERNAME")
  val pass = sys.env.get("SONATYPE_PASSWORD")
  (user, pass) match {
    case (Some(u), Some(p)) =>
      Seq(Credentials("Sonatype Nexus Repository Manager", "s01.oss.sonatype.org", u, p))
    case _ => Nil
  }
}

// A non-interactive GPG passphrase for CI; locally sbt-pgp prompts instead.
ThisBuild / pgpPassphrase := sys.env.get("PGP_PASSPHRASE").map(_.toCharArray)

/** One-step release, used by `.github/workflows/release.yml`.
 *
 *  Signing and bundle release are separate tasks; running them as one command
 *  keeps the workflow from half-publishing if the second is forgotten.
 */
addCommandAlias("ci-release-sroof", "; publishSigned; sonatypeBundleRelease")

// Settings for `scalaApi`: the developer-facing DSL must stay (near-)dependency-free
// so that user projects pick up nothing but the marker types.  No cats.
val apiSettings = Seq(
  scalaVersion := scala3Version,
  version := "0.37.0",
  organization := "io.sroof",
  libraryDependencies += "org.scalameta" %% "munit" % munitVersion % Test,
  testFrameworks += new TestFramework("munit.Framework"),
  scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
)

/** Colon-separated `-Xplugin:` classpath for the sroof compiler plugin.
 *
 *  The head entry must be the packaged plugin JAR: dotc's `Plugin.loadAllFrom`
 *  scans the entries in order for `plugin.properties` and uses the whole list as
 *  the plugin's URLClassLoader URLs.  Compiler jars are excluded on purpose —
 *  they are supplied by the parent (compiler) classloader, and duplicating them
 *  in the child loader risks two incompatible copies of `dotty.tools.*`.
 */
lazy val sroofPluginClasspath = taskKey[String]("-Xplugin: classpath for the sroof compiler plugin")

// Scala Native settings for native sub-projects.
// Uses %%% so cats-core and munit resolve as native artifacts.
val nativeCommonSettings = Seq(
  scalaVersion := scala3Version,
  version := "0.37.0",
  organization := "io.sroof",
  libraryDependencies ++= Seq(
    "org.typelevel" %%% "cats-core" % catsVersion,
    "org.scalameta" %%% "munit"     % munitVersion % Test,
  ),
  testFrameworks += new TestFramework("munit.Framework"),
  scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
)

// Optimised native binary config (applied only to cliNative)
val nativeLinkSettings = Seq(
  nativeConfig ~= {
    _.withLTO(LTO.thin)
     .withMode(Mode.releaseFast)   // releaseFull is slower to link; swap when releasing
     .withGC(GC.immix)
  },
)

// ---- Helper: share JVM project sources with a native sibling ----
// Usage: .settings(shareSourcesWith(someJvmProject))
def shareSourcesWith(jvmProject: Project): Seq[Setting[?]] = Seq(
  Compile / unmanagedSourceDirectories +=
    (jvmProject / Compile / sourceDirectory).value,
  Test / unmanagedSourceDirectories +=
    (jvmProject / Test / sourceDirectory).value,
)

// ---- Root aggregate (JVM only by default) ----
lazy val root = project.in(file("."))
  .aggregate(core, nbe, checker, tactic, syntax, extract, kernel, cli,
             scalaApi, scalaFrontend, scalaPlugin, scalaExamples, scalaIt)
  .settings(
    name := "sroof",
    publish / skip := true,
  )

// Root aggregate for all Native projects — run explicitly:
//   sbt nativeRoot/compile  or  sbt nativeRoot/test
lazy val nativeRoot = project.in(file("native-root"))
  .aggregate(coreNative, nbeNative, checkerNative, tacticNative,
             syntaxNative, extractNative, kernelNative, cliNative)
  .settings(
    name := "sroof-native",
    publish / skip := true,
    // Exclude from the default `sbt test` run so LLVM is optional
    aggregate := false,
  )

// ============================================================
// JVM projects
// ============================================================

lazy val core = project.in(file("core"))
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-core")

lazy val nbe = project.in(file("eval"))
  .dependsOn(core)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-eval")

lazy val checker = project.in(file("checker"))
  .dependsOn(nbe)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-checker")

lazy val tactic = project.in(file("tactic"))
  .dependsOn(checker)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-tactic")

lazy val syntax = project.in(file("syntax"))
  .dependsOn(core)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(
    name := "sroof-syntax",
    libraryDependencies += "com.github.j-mie6" %% "parsley" % parsleyVersion,
  )

lazy val extract = project.in(file("extract"))
  .dependsOn(checker, tactic)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-extract")

lazy val kernel = project.in(file("kernel"))
  .dependsOn(checker, tactic)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-kernel")

lazy val cli = project.in(file("cli"))
  .dependsOn(syntax, tactic, extract, kernel)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(
    name := "sroof-cli",
    Compile / mainClass := Some("sroof.Main"),
  )

// ============================================================
// Scala 3 frontend (the new primary verification path)
//
// scalaApi       — annotations + DSL, compiled into user code
// scalaFrontend  — dotc-independent IR, core translation, proof runner, kernel gate
// scalaPlugin    — the standard Scala 3 compiler plugin (compiler-version-specific)
// scalaExamples  — real .scala sources compiled WITH the plugin enabled
// scalaIt        — integration tests driving a genuine compiler invocation
//
// None of these are mirrored into `nativeRoot`: the plugin links against the
// JVM-only Scala 3 compiler.
// ============================================================

lazy val scalaApi = project.in(file("scala-api"))
  .settings(apiSettings)
  .settings(publishSettings)
  .settings(name := "sroof-scala-api")

lazy val scalaFrontend = project.in(file("scala-frontend"))
  .dependsOn(kernel)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(name := "sroof-scala-frontend")

lazy val scalaPlugin = project.in(file("scala-plugin"))
  .dependsOn(scalaFrontend)
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(
    name := "sroof-scala-plugin",
    // The plugin is compiled against — and only works with — this exact compiler.
    libraryDependencies += "org.scala-lang" %% "scala3-compiler" % scala3Version % "provided",
    sroofPluginClasspath := {
      val pluginJar = (Compile / packageBin).value
      val deps      = (Compile / dependencyClasspath).value.map(_.data)
      val compilerArtifacts =
        Set("scala3-compiler", "scala3-interfaces", "tasty-core", "scala-asm",
            "compiler-interface", "util-interface")
      val runtimeDeps = deps.filterNot(f => compilerArtifacts.exists(f.getName.startsWith))
      (pluginJar +: runtimeDeps).map(_.getAbsolutePath).mkString(java.io.File.pathSeparator)
    },
  )

lazy val scalaExamples = project.in(file("examples-scala3"))
  .dependsOn(scalaApi)
  .settings(apiSettings)
  // Examples are compiled and verified on every build, but they are not a
  // library anyone depends on.
  .settings(noPublishSettings)
  .settings(
    name := "sroof-scala-examples",
    // Verification happens here: if a @theorem fails, this project fails to compile.
    Compile / scalacOptions += "-Xplugin:" + (scalaPlugin / sroofPluginClasspath).value,
  )

lazy val scalaIt = project.in(file("scala-it"))
  .dependsOn(scalaFrontend % Test, extract % Test, syntax % Test)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    name := "sroof-scala-it",
    // Integration tests invoke dotc in-process, so the compiler is a test dependency.
    libraryDependencies += "org.scala-lang" %% "scala3-compiler" % scala3Version % Test,
    // Hand the test harness the exact classpaths sbt built, rather than guessing paths.
    Test / resourceGenerators += Def.task {
      val out       = (Test / resourceManaged).value / "sroof-it.properties"
      val pluginCp  = (scalaPlugin / sroofPluginClasspath).value
      val compileCp = (scalaApi / Compile / fullClasspath).value
                        .map(_.data.getAbsolutePath).mkString(java.io.File.pathSeparator)
      IO.write(out, s"pluginClasspath=$pluginCp\ncompileClasspath=$compileCp\n")
      Seq(out)
    }.taskValue,
  )

// ============================================================
// Scala Native projects
//
// Each native project:
//   - lives in a stub directory (no source files of its own)
//   - shares sources from the JVM counterpart via unmanagedSourceDirectories
//   - uses %%% for cross-platform deps
//
// PREREQUISITES (Ubuntu/WSL2):
//   sudo apt-get install clang lld libunwind-dev
//
// Build native CLI binary:
//   sbt cliNative/nativeLink
//   ./cli-native/target/scala-3.3.6/sroof-cli-native
// ============================================================

lazy val coreNative = project.in(file("core-native"))
  .enablePlugins(ScalaNativePlugin)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(core))
  .settings(name := "sroof-core-native")

lazy val nbeNative = project.in(file("eval-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(coreNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(nbe))
  .settings(name := "sroof-eval-native")

lazy val checkerNative = project.in(file("checker-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(nbeNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(checker))
  .settings(name := "sroof-checker-native")

lazy val tacticNative = project.in(file("tactic-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(checkerNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(tactic))
  .settings(name := "sroof-tactic-native")

lazy val syntaxNative = project.in(file("syntax-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(coreNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(syntax))
  .settings(
    name := "sroof-syntax-native",
    libraryDependencies += "com.github.j-mie6" %%% "parsley" % parsleyVersion,
  )

lazy val extractNative = project.in(file("extract-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(checkerNative, tacticNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(extract))
  .settings(name := "sroof-extract-native")

lazy val kernelNative = project.in(file("kernel-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(checkerNative, tacticNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(kernel))
  .settings(name := "sroof-kernel-native")

lazy val cliNative = project.in(file("cli-native"))
  .enablePlugins(ScalaNativePlugin)
  .dependsOn(syntaxNative, tacticNative, extractNative, kernelNative)
  .settings(nativeCommonSettings)
  .settings(shareSourcesWith(cli))
  .settings(nativeLinkSettings)
  .settings(
    name := "sroof-cli-native",
    Compile / mainClass := Some("sroof.Main"),
  )
