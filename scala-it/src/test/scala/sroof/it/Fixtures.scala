package sroof.it

/** Source fragments shared by the integration suites.
 *
 *  These live as strings rather than as files in a source directory so that
 *  deliberately invalid fixtures cannot break the ordinary sbt build.
 */
object Fixtures:

  /** The Nat enum and `plus`, the basis of most fixtures. */
  val natPreamble: String =
    """  enum Nat:
      |    case Zero
      |    case Succ(n: Nat)
      |
      |  import Nat.*
      |
      |  def plus(n: Nat, m: Nat): Nat =
      |    n match
      |      case Zero    => m
      |      case Succ(k) => Succ(plus(k, m))
      |""".stripMargin

  /** Wrap declarations in a `@proofModule` named `M`, with Nat and plus. */
  def module(members: String, name: String = "M"): String =
    s"""@proofModule
       |object $name:
       |$natPreamble
       |$members
       |""".stripMargin

  /** Wrap declarations in a `@proofModule` with no predefined Nat. */
  def bareModule(members: String, name: String = "M"): String =
    s"""@proofModule
       |object $name:
       |$members
       |""".stripMargin
