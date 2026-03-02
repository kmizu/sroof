package sproof.agent

import munit.FunSuite
import sproof.Main

/** Tests for the proof agent's search loop.
 *
 *  Strategy: run the agent on .sproof source with sorry proofs
 *  and verify it produces ok:true with no warnings.
 */
class SearchLoopSuite extends FunSuite:

  // Helper: run agent on source, return repaired source
  private def repairSource(src: String): String =
    FileRepairer.repair(src, "<test>")

  // Helper: check that repaired source verifies cleanly
  private def verifies(src: String): Boolean =
    Main.processSourceWithWarnings(src, "<test>") match
      case Right((_, _, warnings)) => warnings.isEmpty
      case Left(_)                 => false

  test("agent proves trivial sorry: plus(0, n) = n"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent proves induction sorry: plus(n, 0) = n"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent proves mult_zero: mult(n, 0) = 0"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      def mult(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => Nat.zero
          case Nat.succ(k) => plus(m, mult(k, m))
        }
      }
      defspec mult_zero(n: Nat): mult(n, Nat.zero) = Nat.zero {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent leaves non-sorry proofs untouched"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n {
        by trivial
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired))
    assert(repaired.contains("by trivial"), "non-sorry proof should be unchanged")

  test("agent proves plus_succ_right: plus(n, succ(m)) = succ(plus(n, m))"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_succ_right(n: Nat, m: Nat): plus(n, Nat.succ(m)) = Nat.succ(plus(n, m)) {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent repairs multiple sorry defspecs in one file"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n {
        by sorry
      }
      defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")
    assert(!repaired.contains("by sorry"), "all sorrys should be replaced")

  test("agent proves plus_assoc: plus(plus(a, b), c) = plus(a, plus(b, c))"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_assoc(a: Nat, b: Nat, c: Nat): plus(plus(a, b), c) = plus(a, plus(b, c)) {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent proves plus_zero_symm: n = plus(n, 0)"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_symm(n: Nat): n = plus(n, Nat.zero) {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")

  test("agent proves plus_comm: plus(n, m) = plus(m, n) using helper specs"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_symm(n: Nat): n = plus(n, Nat.zero) {
        by sorry
      }
      defspec plus_succ_right(n: Nat, m: Nat): plus(n, Nat.succ(m)) = Nat.succ(plus(n, m)) {
        by sorry
      }
      defspec plus_comm(n: Nat, m: Nat): plus(n, m) = plus(m, n) {
        by sorry
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired), s"repaired source failed:\n$repaired")
    assert(!repaired.contains("by sorry"), "all sorrys should be replaced")

  test("agent reports success for already-valid file"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n {
        by trivial
      }
      defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
        by induction n {
          case zero    => trivial
          case succ k ih => simplify [ih]
        }
      }
    """
    val repaired = repairSource(src)
    assert(verifies(repaired))
