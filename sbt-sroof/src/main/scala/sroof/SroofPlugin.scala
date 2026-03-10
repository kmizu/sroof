package sroof

import sbt._
import sbt.Keys._
import sbt.plugins.JvmPlugin

import scala.sys.process._
import java.io.File

object SroofPlugin extends AutoPlugin {
  override def requires = JvmPlugin
  override def trigger  = noTrigger  // opt-in: enablePlugins(SroofPlugin)

  object autoImport {
    // Tasks
    val sroofCheck   = taskKey[Unit]("Type-check all .sroof files in sroofSources")
    val sroofExtract = taskKey[Seq[File]]("Extract .sroof files to Scala 3 source (wired into compile)")
    val sroofRepl    = inputKey[Unit]("Start the sroof interactive REPL")

    // Settings
    val sroofSources  = settingKey[Seq[File]]("Directories containing .sroof source files")
    val sroofOutput   = settingKey[File]("Output directory for extracted Scala sources")
    val sroofVersion  = settingKey[String]("Version of the sroof CLI to use")
    val sroofJar      = settingKey[Option[File]]("Path to the sroof CLI uber-JAR (None = use `sroof` on PATH)")
    val sroofJvmOpts  = settingKey[Seq[String]]("JVM options when forking the sroof CLI")
  }

  import autoImport._

  // ---- Helpers ----

  /** Build the command prefix: `java [opts] -jar <jar>` or `["sroof"]`. */
  private def sroofCmd(jar: Option[File], jvmOpts: Seq[String]): Seq[String] =
    jar match {
      case Some(j) => Seq("java") ++ jvmOpts ++ Seq("-jar", j.getAbsolutePath)
      case None    => Seq("sroof")
    }

  /** Run a sroof CLI command, streaming output to the sbt logger. Returns exit code. */
  private def runSroof(
      args:    Seq[String],
      jar:     Option[File],
      jvmOpts: Seq[String],
      log:     Logger,
  ): Int = {
    val cmd = sroofCmd(jar, jvmOpts) ++ args
    log.debug(s"sroof: executing: ${cmd.mkString(" ")}")
    val logger = ProcessLogger(
      out => log.info(s"  $out"),
      err => log.warn(s"  $err"),
    )
    Process(cmd).!(logger)
  }

  // ---- Default settings ----

  override lazy val projectSettings: Seq[Setting[?]] = Seq(
    sroofVersion := "0.1.0",
    sroofSources := Seq(sourceDirectory.value / "main" / "sroof"),
    sroofOutput  := (Compile / sourceManaged).value / "sroof",
    sroofJar     := None,
    sroofJvmOpts := Seq("-Xss8m"),

    // ---- sroofCheck ----
    sroofCheck := {
      val log      = streams.value.log
      val jar      = sroofJar.value
      val jvmOpts  = sroofJvmOpts.value
      val files    = sroofSources.value.flatMap { dir =>
        if (dir.exists) (dir ** "*.sroof").get else Seq.empty
      }

      if (files.isEmpty) {
        log.info("sroof: No .sroof files found.")
      } else {
        log.info(s"sroof: Checking ${files.length} file(s)...")
        val failed = files.filterNot { f =>
          val code = runSroof(Seq("check", f.getAbsolutePath), jar, jvmOpts, log)
          code == 0
        }
        if (failed.nonEmpty) {
          sys.error(s"sroof: ${failed.length} file(s) failed type-checking:\n" +
            failed.map("  " + _.getAbsolutePath).mkString("\n"))
        } else {
          log.success(s"sroof: All ${files.length} file(s) passed.")
        }
      }
    },

    // ---- sroofExtract ----
    sroofExtract := {
      val log      = streams.value.log
      val jar      = sroofJar.value
      val jvmOpts  = sroofJvmOpts.value
      val outDir   = sroofOutput.value
      val files    = sroofSources.value.flatMap { dir =>
        if (dir.exists) (dir ** "*.sroof").get else Seq.empty
      }

      IO.createDirectory(outDir)

      val generated: Seq[File] = files.map { src =>
        val outFile = outDir / src.getName.replace(".sroof", ".scala")
        // Only re-extract if source is newer than the generated file.
        if (!outFile.exists || src.lastModified > outFile.lastModified) {
          log.info(s"sroof: Extracting ${src.getName} → ${outFile.getName}")
          val code = runSroof(
            Seq("extract", src.getAbsolutePath, "--output", outFile.getAbsolutePath),
            jar,
            jvmOpts,
            log,
          )
          if (code != 0)
            sys.error(s"sroof: Extraction failed for ${src.getAbsolutePath}")
        } else {
          log.debug(s"sroof: ${src.getName} is up to date, skipping extraction.")
        }
        outFile
      }

      generated
    },

    // Hook sroofExtract into the compile cycle so `sbt compile` runs it automatically.
    Compile / sourceGenerators += sroofExtract.taskValue,

    // ---- sroofRepl ----
    sroofRepl := {
      val log     = streams.value.log
      val jar     = sroofJar.value
      val jvmOpts = sroofJvmOpts.value
      log.info("Starting sroof REPL (press Ctrl-D or type :quit to exit)...")
      val cmd = sroofCmd(jar, jvmOpts) ++ Seq("repl")
      log.debug(s"sroof: executing: ${cmd.mkString(" ")}")
      Process(cmd).!
      ()
    },
  )
}
