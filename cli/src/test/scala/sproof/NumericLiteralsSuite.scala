package sproof

import munit.FunSuite

/** Tests for numeric literal sugar, == equality syntax, and no-param defspecs.
 *
 *  Numeric literals: `2` elaborates to `Nat.succ(Nat.succ(Nat.zero))` etc.
 *  `==` is a synonym for `=` in proposition/type positions.
 *  `defspec foo: prop { ... }` is valid without a parameter list.
 */
class NumericLiteralsSuite extends FunSuite:

  private val preamble = """
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
  """

  private def check(src: String): Either[String, ?] =
    Main.processSource(src, "<NumericLiteralsSuite>")

  // ---- Numeric literals in expressions ----

  test("0 elaborates to Nat.zero in expression position"):
    val src = preamble + """
      defspec zero_lit(n: Nat): plus(0, n) = n {
        by trivial
      }
    """
    assert(check(src).isRight, s"0 in expression should work: ${check(src)}")

  test("1 elaborates to Nat.succ(Nat.zero) in expression position"):
    val src = preamble + """
      defspec one_lit(n: Nat): plus(1, n) = Nat.succ(n) {
        by trivial
      }
    """
    assert(check(src).isRight, s"1 in expression should work: ${check(src)}")

  // ---- Numeric literals in proposition position ----

  test("numeric literal on LHS of = in proposition"):
    val src = preamble + """
      defspec lhs_lit(n: Nat): plus(2, n) = Nat.succ(Nat.succ(n)) {
        by trivial
      }
    """
    assert(check(src).isRight, s"numeric literal on LHS should work: ${check(src)}")

  test("numeric literal on RHS of = in proposition"):
    val src = preamble + """
      defspec rhs_lit: plus(Nat.succ(Nat.succ(Nat.zero)), Nat.succ(Nat.succ(Nat.succ(Nat.zero)))) = 5 {
        by trivial
      }
    """
    assert(check(src).isRight, s"numeric literal on RHS should work: ${check(src)}")

  test("numeric literals on both sides of = in proposition"):
    val src = preamble + """
      defspec both_lit: plus(2, 3) = 5 {
        by trivial
      }
    """
    assert(check(src).isRight, s"numeric literals on both sides should work: ${check(src)}")

  test("larger numeric literal: plus(10, 5) = 15"):
    val src = preamble + """
      defspec large_lit: plus(10, 5) = 15 {
        by trivial
      }
    """
    assert(check(src).isRight, s"larger literals should work: ${check(src)}")

  test("wrong numeric literal is rejected"):
    val src = preamble + """
      defspec wrong_lit: plus(2, 3) = 6 {
        by trivial
      }
    """
    assert(check(src).isLeft, "wrong literal value should fail")

  // ---- == as synonym for = ----

  test("== accepted in proposition: ground theorem"):
    val src = preamble + """
      defspec refl_lit: 1 == 1 {
        by trivial
      }
    """
    assert(check(src).isRight, s"== in ground theorem should work: ${check(src)}")

  test("== accepted in proposition: parameterized"):
    val src = preamble + """
      defspec plus_zero_left_eq(m: Nat): plus(0, m) == m {
        by trivial
      }
    """
    assert(check(src).isRight, s"== with params should work: ${check(src)}")

  test("== with numeric literals on both sides"):
    val src = preamble + """
      defspec two_plus_three_eq: plus(2, 3) == 5 {
        by trivial
      }
    """
    assert(check(src).isRight, s"== with numeric literals should work: ${check(src)}")

  test("wrong == proposition is rejected"):
    val src = preamble + """
      defspec bad_eq: plus(2, 3) == 4 {
        by trivial
      }
    """
    assert(check(src).isLeft, "wrong == proposition should fail")

  // ---- No-param defspecs (ground theorems) ----

  test("defspec with no params and = proposition"):
    val src = preamble + """
      defspec ground_eq: plus(0, 0) = 0 {
        by trivial
      }
    """
    assert(check(src).isRight, s"no-param defspec with = should work: ${check(src)}")

  test("defspec with no params and == proposition"):
    val src = preamble + """
      defspec ground_eq2: plus(0, 0) == 0 {
        by trivial
      }
    """
    assert(check(src).isRight, s"no-param defspec with == should work: ${check(src)}")

  test("theorem keyword also accepts no params"):
    val src = preamble + """
      theorem ground_thm: plus(1, 1) = 2 {
        by trivial
      }
    """
    assert(check(src).isRight, s"theorem with no params should work: ${check(src)}")

  test("no-param defspec with non-trivial goal is rejected"):
    val src = preamble + """
      defspec impossible: plus(0, 0) = 1 {
        by trivial
      }
    """
    assert(check(src).isLeft, "ground theorem with false proposition should fail")