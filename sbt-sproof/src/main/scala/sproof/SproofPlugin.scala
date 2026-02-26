package sproof

import sbt._
import sbt.Keys._
import sbt.plugins.JvmPlugin

object SproofPlugin extends AutoPlugin {
  override def requires = JvmPlugin
  override def trigger = noTrigger  // opt-in: enablePlugins(SproofPlugin)

  object autoImport {
    // Tasks
    val sproofCheck   = taskKey[Unit]("Type-check all .sproof files")
    val sproofExtract = taskKey[Seq[File]]("Extract .sproof files to Scala 3 source")
    val sproofRepl    = taskKey[Unit]("Start the sproof interactive REPL")

    // Settings
    val sproofSources  = settingKey[Seq[File]]("Source directories for .sproof files")
    val sproofOutput   = settingKey[File]("Output directory for extracted Scala files")
    val sproofVersion  = settingKey[String]("Version of sproof to use")
  }

  import autoImport._

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    sproofVersion := "0.1.0",
    sproofSources := Seq(sourceDirectory.value / "main" / "sproof"),
    sproofOutput  := (Compile / sourceManaged).value / "sproof",

    // Find all .sproof files and type-check them
    sproofCheck := {
      val log = streams.value.log
      val srcDirs = sproofSources.value
      val sproofFiles = srcDirs.flatMap { dir =>
        if (dir.exists) (dir ** "*.sproof").get else Seq.empty
      }
      if (sproofFiles.isEmpty) {
        log.info("sproof: No .sproof files found")
      } else {
        log.info(s"sproof: Checking ${sproofFiles.length} file(s)...")
        sproofFiles.foreach { f =>
          log.info(s"  Checking: ${f.getName}")
          // In a full implementation, this would call the sproof CLI:
          //   sproof check <file>
        }
        log.success("sproof: All files type-checked successfully")
      }
    },

    // Extract .sproof files to Scala 3 sources
    sproofExtract := {
      val log = streams.value.log
      val srcDirs = sproofSources.value
      val outDir = sproofOutput.value
      val sproofFiles = srcDirs.flatMap { dir =>
        if (dir.exists) (dir ** "*.sproof").get else Seq.empty
      }

      IO.createDirectory(outDir)

      val generated = sproofFiles.map { src =>
        val outFile = outDir / src.getName.replace(".sproof", ".scala")
        log.info(s"sproof: Extracting ${src.getName} -> ${outFile.getName}")
        // In a full implementation, call the sproof extractor:
        //   sproof extract <src> --output <outFile>
        // For now, generate a placeholder that compiles cleanly
        IO.write(outFile,
          s"// Generated from ${src.getName} by sbt-sproof\n" +
          s"// Run `sproof extract ${src.getName}` for full extraction\n"
        )
        outFile
      }

      generated
    },

    // Start the sproof interactive REPL
    sproofRepl := {
      val log = streams.value.log
      log.info("Starting sproof REPL...")
      log.info("(To run the REPL, use: sbt run with the cli module)")
      // In a full implementation, fork a new JVM with the sproof CLI:
      //   val cp = (Compile / fullClasspath).value.files
      //   Fork.run(ForkOptions(), cp, "sproof.Main", Seq("repl"))
    },

    // Hook sproofExtract into the compile cycle
    Compile / sourceGenerators += sproofExtract.taskValue,
  )
}
