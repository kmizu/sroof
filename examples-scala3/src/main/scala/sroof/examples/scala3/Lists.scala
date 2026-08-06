package sroof.examples.scala3

import sroof.annotation.*
import sroof.lang.*

/** Elementary list theorems over a **generic** enum.
 *
 *  The list is `Lst[A]` for an arbitrary element type, so these are the usual
 *  textbook statements rather than facts about one concrete element type.
 *  Induction over a parameterised inductive became possible in v0.7.
 */
@proofModule
object Lists:

  enum Nat:
    case Zero
    case Succ(n: Nat)

  enum Lst[A]:
    case Nil()
    case Cons(head: A, tail: Lst[A])

  import Nat.*, Lst.*

  def append[A](xs: Lst[A], ys: Lst[A]): Lst[A] =
    xs match
      case Nil()      => ys
      case Cons(h, t) => Cons(h, append(t, ys))

  def length[A](xs: Lst[A]): Nat =
    xs match
      case Nil()      => Zero
      case Cons(_, t) => Succ(length(t))

  def plus(n: Nat, m: Nat): Nat =
    n match
      case Zero    => m
      case Succ(k) => Succ(plus(k, m))

  // ---- append: the unit laws ----
  //
  // The left one holds by computation — `append` recurses on its first argument,
  // so `append(Nil(), ys)` is just its first branch.  The right one does not:
  // `append(xs, Nil())` is stuck while `xs` is a variable, and needs induction.

  @theorem
  def appendNilLeft[A](ys: Lst[A]): Proof =
    prove(append(Nil[A](), ys) === ys)(trivial)

  @theorem
  def appendNilRight[A](xs: Lst[A]): Proof =
    prove(append(xs, Nil[A]()) === xs)(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      }
    )

  // ---- append is associative ----

  @theorem
  def appendAssoc[A](xs: Lst[A], ys: Lst[A], zs: Lst[A]): Proof =
    prove(append(append(xs, ys), zs) === append(xs, append(ys, zs)))(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      }
    )

  // ---- length distributes over append ----
  //
  // The statement mixes the two enums: a fact about `Lst[A]` whose two sides are
  // `Nat`s.

  @theorem
  def lengthAppend[A](xs: Lst[A], ys: Lst[A]): Proof =
    prove(length(append(xs, ys)) === plus(length(xs), length(ys)))(
      induction(xs) {
        case Nil()      => trivial
        case Cons(h, t) => simplify(ih(t))
      }
    )
