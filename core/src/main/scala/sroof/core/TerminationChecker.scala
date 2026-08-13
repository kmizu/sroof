package sroof.core

/** Structural termination checker for Fix (recursive functions).
 *
 *  Ensures every recursive call is applied to a structurally smaller argument.
 *  "Structurally smaller" means a variable bound by a pattern match on the
 *  decreasing parameter (i.e., a constructor sub-component).
 *
 *  Algorithm:
 *  1. For Fix(f, tpe, body), the body has Var(0) = f (self-reference).
 *  2. Walk under the lambdas to the match that takes a parameter apart. **That
 *     parameter's position is the decreasing one** — call it `p`.
 *  3. For each recursive call f(a1)(a2)...(an), verify that `a_p` specifically
 *     is a structurally smaller variable, and that the other arguments do not
 *     contain an unguarded reference to f.
 *
 *  This supports multi-argument functions where any argument may be the
 *  decreasing one (e.g. `matches(derive(r,c), t)` where t, not r, decreases) —
 *  the match picks it out.
 *
 *  Step 3 used to accept a call where *any* argument was smaller, which does not
 *  imply termination: `def loop(n, m) = match m { case succ(k) => loop(k, m) }`
 *  passes a subterm of `m` in `n`'s position while `m` itself never shrinks, and
 *  loops forever. Step 2's scrutinee check is likewise load-bearing: the
 *  scrutinee was not looked at, so `match loop(n) { ... }` — a recursive call
 *  with nothing guarding it — was accepted. Either one certifies a
 *  non-terminating definition, which in a dependent type theory proves False.
 *  See CHANGELOG v0.35.0.
 *
 *  This is a simplified version of Coq's guard condition.
 */
object TerminationChecker:

  /** Check that a term satisfies the structural recursion guard.
   *
   *  Only Fix terms are checked; all other terms pass trivially.
   */
  def check(t: Term)(using env: GlobalEnv): Either[String, Unit] =
    t match
      case Term.Fix(name, tpe, body) =>
        // fixIdx = 0 in body (the self-reference De Bruijn index at depth 0)
        checkBody(name, fixIdx = 0, body)
      case _ =>
        Right(())

  /** Check the body of a Fix for guarded recursion.
   *
   *  `fixIdx` is the De Bruijn index of the fixpoint self-reference at the
   *  current depth. It increases as we go under binders.
   */
  private def checkBody(name: String, fixIdx: Int, body: Term): Either[String, Unit] =
    body match
      // Lambda: the main case. We look for the pattern:
      //   λx. match x { case C(y1..yn) => ...f(yi)... }
      case Term.Lam(_, tp, lamBody) =>
        // A parameter type is part of the body too. A signature cannot mention
        // the function being defined, so this only ever fires on a term the
        // front end should not have produced — but it costs nothing to say so.
        if containsFixRef(tp, fixIdx) then
          Left(s"Termination check failed: '$name' appears in a parameter type")
        else
          // Under this lambda, fixIdx shifts up by 1
          checkBody(name, fixIdx + 1, lamBody)

      // Match: binds constructor sub-components as smaller variables
      case Term.Mat(scrutinee, cases, rt) =>
        // The scrutinee and the return type are part of the body. A recursive
        // call in either is unguarded — and a match with no cases has no branch
        // to catch it, so skipping them accepted `match f(n) { }` outright.
        if containsFixRef(scrutinee, fixIdx) then
          Left(s"Termination check failed: '$name' is called in the scrutinee of a match")
        else if containsFixRef(rt, fixIdx) then
          Left(s"Termination check failed: '$name' appears in the return type of a match")
        else
          // Which parameter is taken apart decides which argument position has
          // to shrink. `fixIdx` is the number of lambdas walked under, so the
          // i-th parameter (outermost first) is Var(fixIdx - 1 - i). A scrutinee
          // bound outside this Fix is nobody's parameter and yields no measure.
          val decrPos: Option[Int] = scrutinee match
            case Term.Var(i) if i < fixIdx => Some(fixIdx - 1 - i)
            case _                         => None

          cases.foldLeft[Either[String, Unit]](Right(())) { (acc, mc) =>
            acc.flatMap { _ =>
              // Inside this case branch, fixIdx shifts by mc.bindings
              val newFixIdx = fixIdx + mc.bindings
              // The constructor-bound variables (Var(0)..Var(mc.bindings-1))
              // are structurally smaller than the scrutinee
              val smallerVars: Set[Int] =
                if decrPos.isDefined then (0 until mc.bindings).toSet else Set.empty
              checkGuarded(name, newFixIdx, mc.body, smallerVars, decrPos)
            }
          }

      // If the body is just a reference to f with no lambda wrapping, that's
      // a bare self-reference (non-terminating)
      case Term.Var(i) if i == fixIdx =>
        Left(s"Termination check failed: '$name' is used as a bare value (no guarded recursion)")

      // App at top level (not inside a match) — check if it's a recursive call
      case Term.App(fn, _) if containsFixRef(fn, fixIdx) =>
        Left(s"Termination check failed: '$name' makes a recursive call outside of a match case")

      // Other terms at the top level — check that f doesn't escape
      case _ =>
        if containsUnguardedRef(body, fixIdx) then
          Left(s"Termination check failed: '$name' has unguarded recursive reference")
        else
          Right(())

  /** Peel a curried application into (function, args): App(App(f, a1), a2) → (f, [a1, a2]). */
  private def peelArgs(t: Term): (Term, List[Term]) =
    def go(t: Term, acc: List[Term]): (Term, List[Term]) = t match
      case Term.App(fn, arg) => go(fn, arg :: acc)
      case other             => (other, acc)
    go(t, Nil)

  /** Check that all recursive calls in `t` are to structurally smaller arguments.
   *
   *  `smallerVars` contains the De Bruijn indices (at current depth) of variables
   *  that are structurally smaller than the decreasing argument.
   *
   *  `decrPos` is the argument position the top-level match took apart. For a call
   *  f(a1)(a2)...(an) we accept only if `a_decrPos` is a structurally smaller
   *  variable, and the other arguments don't contain unguarded fix references.
   *  A smaller value in some *other* position is not progress: the scrutinised
   *  argument would be passed along unchanged and the function would loop.
   */
  private def checkGuarded(
    name: String, fixIdx: Int, t: Term, smallerVars: Set[Int], decrPos: Option[Int],
  ): Either[String, Unit] =
    t match
      case Term.Var(i) if i == fixIdx =>
        // Bare reference to f without application — this is a higher-order escape
        Left(s"Termination check failed: '$name' escapes as a value in a match branch")

      case app @ Term.App(_, _) =>
        val (fn, args) = peelArgs(app)
        fn match
          case Term.Var(fIdx) if fIdx == fixIdx =>
            // Recursive call f(a1)(a2)...(an): the argument in the decreasing
            // position must be a smaller variable; the rest must not contain
            // unguarded fix references.
            val smallerHere = decrPos.flatMap(args.lift).exists {
              case Term.Var(i) => smallerVars.contains(i)
              case _           => false
            }
            if !smallerHere then
              decrPos match
                case Some(p) =>
                  Left(
                    s"Termination check failed: '$name' matches on argument ${p + 1}, so the " +
                    s"recursive call must pass a structurally smaller value in that position"
                  )
                case None =>
                  Left(s"Termination check failed: '$name' is called with a non-structurally-smaller argument")
            else
              val otherArgs = args.zipWithIndex.filterNot(_._2 == decrPos.get).map(_._1)
              otherArgs.foldLeft[Either[String, Unit]](Right(())) { (acc, a) =>
                acc.flatMap(_ => checkGuarded(name, fixIdx, a, smallerVars, decrPos))
              }
          case _ =>
            // Non-recursive application: check fn and all args
            for
              _ <- checkGuarded(name, fixIdx, fn, smallerVars, decrPos)
              _ <- args.foldLeft[Either[String, Unit]](Right(())) { (acc, a) =>
                     acc.flatMap(_ => checkGuarded(name, fixIdx, a, smallerVars, decrPos))
                   }
            yield ()

      case Term.Lam(_, tp, body) =>
        for
          _ <- checkGuarded(name, fixIdx, tp, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx + 1, body, smallerVars.map(_ + 1), decrPos)
        yield ()

      case Term.Pi(_, dom, cod) =>
        for
          _ <- checkGuarded(name, fixIdx, dom, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx + 1, cod, smallerVars.map(_ + 1), decrPos)
        yield ()

      case Term.Let(_, tp, defn, body) =>
        for
          _ <- checkGuarded(name, fixIdx, tp, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx, defn, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx + 1, body, smallerVars.map(_ + 1), decrPos)
        yield ()

      case Term.Con(_, _, args) =>
        args.foldLeft[Either[String, Unit]](Right(())) { (acc, arg) =>
          acc.flatMap(_ => checkGuarded(name, fixIdx, arg, smallerVars, decrPos))
        }

      case Term.Mat(scrut, cases, rt) =>
        for
          _ <- checkGuarded(name, fixIdx, scrut, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx, rt, smallerVars, decrPos)
          _ <- cases.foldLeft[Either[String, Unit]](Right(())) { (acc, mc) =>
            acc.flatMap { _ =>
              val n = mc.bindings
              val newFixIdx = fixIdx + n
              // Constructor-bound vars are smaller if scrutinee is smaller
              val scrutSmaller = scrut match
                case Term.Var(si) if smallerVars.contains(si) =>
                  (0 until n).toSet
                case _ => Set.empty[Int]
              val newSmaller = smallerVars.map(_ + n) ++ scrutSmaller
              checkGuarded(name, newFixIdx, mc.body, newSmaller, decrPos)
            }
          }
        yield ()

      case Term.Fix(_, tp, body) =>
        for
          _ <- checkGuarded(name, fixIdx, tp, smallerVars, decrPos)
          _ <- checkGuarded(name, fixIdx + 1, body, smallerVars.map(_ + 1), decrPos)
        yield ()

      case _ => Right(())  // Var (not fixIdx), Uni, Meta, Ind

  /** Check if a term contains a reference to the fixpoint at the given index. */
  private def containsFixRef(t: Term, fixIdx: Int): Boolean = t match
    case Term.Var(i)            => i == fixIdx
    case Term.App(fn, arg)      => containsFixRef(fn, fixIdx) || containsFixRef(arg, fixIdx)
    case Term.Lam(_, tp, b)    => containsFixRef(tp, fixIdx) || containsFixRef(b, fixIdx + 1)
    case Term.Pi(_, d, c)      => containsFixRef(d, fixIdx) || containsFixRef(c, fixIdx + 1)
    case Term.Let(_, t, d, b)  => containsFixRef(t, fixIdx) || containsFixRef(d, fixIdx) || containsFixRef(b, fixIdx + 1)
    case Term.Con(_, _, args)   => args.exists(containsFixRef(_, fixIdx))
    case Term.Mat(s, cs, rt)   => containsFixRef(s, fixIdx) || containsFixRef(rt, fixIdx) || cs.exists(c => containsFixRef(c.body, fixIdx + c.bindings))
    case Term.Fix(_, tp, b)    => containsFixRef(tp, fixIdx) || containsFixRef(b, fixIdx + 1)
    case _                      => false

  /** Check if a term contains an unguarded reference to the fixpoint. */
  private def containsUnguardedRef(t: Term, fixIdx: Int): Boolean =
    containsFixRef(t, fixIdx)
