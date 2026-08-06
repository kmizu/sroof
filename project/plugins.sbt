// Scala Native cross-compilation — Phase 4
addSbtPlugin("org.portable-scala" % "sbt-crossproject" % "1.3.2")
addSbtPlugin("org.scala-native"   % "sbt-scala-native" % "0.5.10")

// Publishing to Maven Central via Sonatype.
// Both are only needed to *release*; ordinary builds do not use them.
addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.12.2")
addSbtPlugin("com.github.sbt" % "sbt-pgp"      % "2.2.1")
