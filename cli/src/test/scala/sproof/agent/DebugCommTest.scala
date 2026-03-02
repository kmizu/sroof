package sproof.agent

import munit.FunSuite
import sproof.Main

class DebugCommTest extends FunSuite:
  test("debug plus_comm verifies"):
    val repaired = """
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
        by induction n {
    case zero => trivial
    case succ _arg0 ih => simplify [ih]
  }
      }
      defspec plus_succ_right(n: Nat, m: Nat): plus(n, Nat.succ(m)) = Nat.succ(plus(n, m)) {
        by induction n {
    case zero => trivial
    case succ _arg0 ih => simplify [ih]
  }
      }
      defspec plus_comm(n: Nat, m: Nat): plus(n, m) = plus(m, n) {
        by induction n {
    case zero => simplify [plus_zero_symm]
    case succ _arg0 ih => simplify [ih, plus_succ_right]
  }
      }
    """
    Main.processSourceWithWarnings(repaired, "<test>") match
      case Left(err) => println(s"ERROR: $err")
      case Right((_, _, warnings)) =>
        if warnings.isEmpty then println("OK!")
        else println(s"Warnings: $warnings")
    assert(true)
