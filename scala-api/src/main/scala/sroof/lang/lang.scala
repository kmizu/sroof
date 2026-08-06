package sroof.lang

/** The sroof proof DSL: ordinary, type-correct Scala 3 that the sroof compiler
 *  plugin recognises **by resolved symbol**, never by spelling.
 *
 *  Everything here lives at the top level of a single file on purpose.  A
 *  top-level `opaque type` is only transparent to definitions in the same
 *  synthetic wrapper object (`sroof.lang.lang$package`), so the DSL bodies below
 *  must sit beside the type declarations to return `()`.
 *
 *  Runtime behaviour: every operation is inert.  `prove` takes both of its
 *  arguments by name and discards them, so no goal or tactic is ever evaluated
 *  at runtime.  There is no reflection and no runtime proof checking — proofs
 *  are decided during compilation or not at all.
 */

/** A proposition.  Built by [[===]]; consumed by [[prove]]. */
opaque type Prop = Unit

/** Evidence that a proposition holds.  The result type of a `@theorem` method. */
opaque type Proof = Unit

/** A proof script.  Built by [[trivial]], [[induction]], [[simplify]]. */
opaque type Tactic = Unit

/** The equality proposition `lhs = rhs`.
 *
 *  Both sides must be verified computations over supported inductive types.
 */
extension [A](lhs: A) infix def ===(rhs: A): Prop = ()

/** State a goal and the script that proves it.
 *
 *  Both arguments are by-name and are never evaluated: this call is a
 *  compile-time declaration, not a computation.
 */
def prove(goal: => Prop)(tactic: => Tactic): Proof = ()

/** Close a goal whose two sides are definitionally equal. */
def trivial: Tactic = ()

/** Structural induction over `value`, which must be a parameter or pattern
 *  binder of a supported inductive type.
 *
 *  Every constructor must be covered exactly once, with no guards and no
 *  pattern alternatives.
 */
def induction[A](value: A)(cases: PartialFunction[A, Tactic]): Tactic = ()

/** Structural induction on `value`, with the hypothesis universally quantified
 *  over the additional parameters in `generalizing`.
 *
 *  Needed when the goal changes those parameters as the recursion proceeds — a
 *  hypothesis fixed at the original values would not apply. The classic case is
 *  commutativity, where the second operand differs at each step.
 *
 *  Every entry in `generalizing` must be another parameter of the same theorem.
 */
def inductionGeneralizing[A](value: A, generalizing: Any*)(
  cases: PartialFunction[A, Tactic]): Tactic = ()

/** Case analysis on `value`, **without** an induction hypothesis.
 *
 *  Same shape as [[induction]], and subject to the same branch rules, but no
 *  hypothesis is generated — so [[ih]] is not available inside a branch. Use
 *  this when the proof needs only to split on constructors.
 */
def cases[A](value: A)(branches: PartialFunction[A, Tactic]): Tactic = ()

/** The induction hypothesis for `value`.
 *
 *  Legal only inside a recursive branch of the enclosing [[induction]], applied
 *  to that branch's recursive field binder.
 */
def ih[A](value: A): Proof = ()

/** Prove an intermediate equation, then continue with it in scope.
 *
 *  Lets a proof be broken into steps instead of being forced through a single
 *  tactic. The hypothesis is bound by the continuation's parameter and can be
 *  cited like any other lemma:
 *
 *  {{{
 *  have(plus(k, Zero) === k)(simplify(ih(k))) { step =>
 *    simplify(step)
 *  }
 *  }}}
 *
 *  The intermediate claim is proved as a goal in its own right, so it is subject
 *  to the same kernel check as everything else.
 */
def have(claim: => Prop)(proof: => Tactic)(continue: Proof => Tactic): Tactic = ()

/** Close the goal with the induction hypothesis for `recursive`, instantiated at
 *  the given values.
 *
 *  The counterpart to [[inductionGeneralizing]]: that combinator makes the
 *  hypothesis universally quantified, and this one applies it. Each entry in
 *  `at` must be a parameter or pattern binder visible in the branch, given in
 *  the same order as the `generalizing` list.
 *
 *  {{{
 *  inductionGeneralizing(n, m) {
 *    case Zero    => trivial
 *    case Succ(k) => exactIh(k)(m)
 *  }
 *  }}}
 */
def exactIh(recursive: Any)(at: Any*): Tactic = ()

/** Rewrite the goal with the given lemmas, then close it. */
def simplify(lemmas: Proof*): Tactic = ()

/** Rewrite the goal with the given equations.
 *
 *  Where [[simplify]] normalises and then closes, this applies the equations as
 *  directed rewrites — useful when the goal needs one specific step rather than
 *  full simplification.
 */
def rewrite(equations: Proof*): Tactic = ()
