package sroof.lang

import munit.FunSuite

/** The DSL must never execute proof content at runtime.
 *
 *  If `prove` evaluated its arguments, a proof script could have side effects —
 *  and, worse, a "proof" could appear to succeed by running code rather than by
 *  passing the kernel.  These tests pin the erasure strategy.
 */
class RuntimeInertSuite extends FunSuite:

  test("prove does not evaluate its goal or its tactic") {
    var evaluated = 0
    def loudGoal: Prop   = { evaluated += 1; 1 === 1 }
    def loudTactic: Tactic = { evaluated += 1; trivial }
    prove(loudGoal)(loudTactic)
    assertEquals(evaluated, 0)
  }

  test("tactic combinators are pure and total") {
    // Called directly (outside prove) they must still be harmless no-ops.
    val t: Tactic = simplify(ih(0))
    val u: Tactic = induction(0) { case _ => trivial }
    assertEquals(t, u)
  }

  test("=== builds a proposition without comparing values") {
    // A false equation is a perfectly good *proposition*; only the kernel decides.
    // Both sides erase to the same inert value, so a false and a true equation
    // are indistinguishable at runtime — as they must be.
    assertEquals(1 === 2, 1 === 1)
  }
