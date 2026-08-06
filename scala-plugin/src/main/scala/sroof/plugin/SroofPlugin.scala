package sroof.plugin

import dotty.tools.dotc.plugins.{PluginPhase, StandardPlugin}

/** The sroof compiler plugin.
 *
 *  A **standard** plugin: it inserts one inspection phase into the normal
 *  pipeline and never replaces Scala's parser or typer.  It reads typed trees,
 *  verifies `@proofModule` objects, and reports; it rewrites nothing.
 *
 *  Enabling it is a build decision.  `@proofModule`/`@theorem` on their own are
 *  inert annotations — without `-Xplugin`, annotated code compiles and runs, but
 *  nothing is proved.
 */
class SroofPlugin extends StandardPlugin:
  val name: String = "sroof"

  override val description: String =
    "verifies @proofModule declarations with the sroof proof kernel"

  /** Returns a freshly constructed phase per compiler run: the phase must not be
   *  reused, and holding one would leak state between runs.
   */
  def init(options: List[String]): List[PluginPhase] = List(new SroofPhase)
