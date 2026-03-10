lazy val root = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
    name := "sbt-sroof",
    organization := "io.sroof",
    version := "0.1.0",
    scalaVersion := "2.12.20",   // sbt plugins use Scala 2.12
    sbtPlugin := true,
    scriptedLaunchOpts += s"-Dplugin.version=${version.value}",
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.0.2" % Test,
    ),
  )
