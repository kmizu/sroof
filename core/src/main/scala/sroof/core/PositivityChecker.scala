package sroof.core

/** Strict positivity checker for inductive type definitions.
 *
 *  An inductive type `T` is strictly positive iff `T` never appears in a
 *  negative position in any constructor argument type. A position is negative
 *  when it is on the left side of an odd number of arrows (Pi domains).
 *
 *  Occurrences of `T` inside the *parameters of another applied inductive* are
 *  the subtle case. `D(T)` is only as positive as `D` is in that parameter:
 *  with `Neg(A) { mk(f: A -> Empty) }`, the type `Neg(T)` contains a function
 *  out of `T`, even though no arrow is visible at the occurrence. Inheriting
 *  the ambient polarity there accepted `Bad { mk(w: Neg(Bad)) }`, from which
 *  `0 = 1` was derivable with no recursion at the term level (v0.36). So a
 *  nested occurrence demands two things: `T` strictly positive *within* the
 *  argument, and the inductive at the head using that parameter strictly
 *  positively in all of its constructors — checked recursively, with a seen-set
 *  so that self-nesting like `List(A)`'s tail terminates. A cycle without a
 *  violation is fine: any genuine violation is a finite path ending at an
 *  arrow, and the traversal flags it before the cycle closes.
 *
 *  Without this check, non-positive types can encode self-application paradoxes
 *  (Girard's paradox), making the logic inconsistent.
 */
object PositivityChecker:

  /** Check that all constructors of the inductive type `indName` are strictly positive.
   *
   *  Needs the environment to look up the constructors of *other* inductives
   *  that `indName` nests inside. The inductive being defined is not in the
   *  environment yet; occurrences of it are matched by name.
   *
   *  @return Right(()) if all constructors pass, Left(error message) otherwise.
   */
  def check(indName: String, ctors: List[CtorDef])(using env: GlobalEnv): Either[String, Unit] =
    ctors.foldLeft[Either[String, Unit]](Right(())) { (acc, ctor) =>
      acc.flatMap { _ =>
        ctor.argTpes.foldLeft[Either[String, Unit]](Right(())) { (acc2, argTpe) =>
          acc2.flatMap(_ => checkPolarity(indName, ctor.name, argTpe, positive = true, Set.empty))
        }
      }
    }

  /** Peel a curried application into (head, args). */
  private def peelSpine(t: Term): (Term, List[Term]) =
    def go(t: Term, acc: List[Term]): (Term, List[Term]) = t match
      case Term.App(fn, arg) => go(fn, arg :: acc)
      case other             => (other, acc)
    go(t, Nil)

  /** Does `Ind(name, …)` occur anywhere in `t`? Name-based, so no depth tracking. */
  private def mentionsInd(name: String, t: Term): Boolean = t match
    case Term.Ind(n, _, _)      => n == name
    case Term.App(f, a)         => mentionsInd(name, f) || mentionsInd(name, a)
    case Term.Lam(_, tp, b)     => mentionsInd(name, tp) || mentionsInd(name, b)
    case Term.Pi(_, d, c)       => mentionsInd(name, d) || mentionsInd(name, c)
    case Term.Let(_, tp, d, b)  => mentionsInd(name, tp) || mentionsInd(name, d) || mentionsInd(name, b)
    case Term.Con(_, _, args)   => args.exists(mentionsInd(name, _))
    case Term.Mat(s, cs, rt)    => mentionsInd(name, s) || mentionsInd(name, rt) || cs.exists(c => mentionsInd(name, c.body))
    case Term.Fix(_, tp, b)     => mentionsInd(name, tp) || mentionsInd(name, b)
    case Term.Var(_) | Term.Uni(_) | Term.Meta(_) => false

  /** Check that `indName` occurs only in strictly positive positions within `tpe`.
   *
   *  Polarity tracks whether we're in a positive (true) or negative (false) position.
   *  - At the top level, polarity is positive.
   *  - In the domain of a Pi (left of arrow), polarity flips.
   *  - In the codomain of a Pi (right of arrow), polarity is preserved.
   *
   *  `seen` carries the (inductive, parameter) pairs already being checked by
   *  [[paramStrictlyPositive]], to terminate on recursive nestings.
   */
  private def checkPolarity(
    indName: String, ctorName: String, tpe: Term, positive: Boolean,
    seen: Set[(String, Int)],
  )(using env: GlobalEnv): Either[String, Unit] =
    tpe match
      case Term.Ind(name, _, _) if name == indName =>
        if positive then Right(())
        else Left(
          s"Strict positivity violation: '$indName' appears in a negative position " +
          s"in constructor '$ctorName'"
        )

      case app @ Term.App(_, _) =>
        val (head, args) = peelSpine(app)
        head match
          case Term.Ind(dName, _, _) =>
            // An applied inductive. The head itself is an occurrence (or not);
            // each argument that mentions `indName` is a *nested* occurrence
            // and must satisfy the nested-positivity rule.
            for
              _ <- checkPolarity(indName, ctorName, head, positive, seen)
              _ <- args.zipWithIndex.foldLeft[Either[String, Unit]](Right(())) {
                     case (acc, (arg, i)) => acc.flatMap { _ =>
                       if !mentionsInd(indName, arg) then Right(())
                       else if !positive then
                         Left(
                           s"Strict positivity violation: '$indName' appears in a negative position " +
                           s"(inside an argument of '$dName') in constructor '$ctorName'"
                         )
                       else
                         for
                           _ <- checkPolarity(indName, ctorName, arg, positive = true, seen)
                           _ <- paramStrictlyPositive(dName, i, indName, ctorName, seen)
                         yield ()
                     }
                   }
            yield ()
          case _ =>
            for
              _ <- checkPolarity(indName, ctorName, head, positive, seen)
              _ <- args.foldLeft[Either[String, Unit]](Right(())) { (acc, a) =>
                     acc.flatMap(_ => checkPolarity(indName, ctorName, a, positive, seen))
                   }
            yield ()

      case Term.Pi(_, dom, cod) =>
        for
          _ <- checkPolarity(indName, ctorName, dom, !positive, seen)
          _ <- checkPolarity(indName, ctorName, cod, positive, seen)
        yield ()

      case Term.Lam(_, tp, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive, seen)
          _ <- checkPolarity(indName, ctorName, body, positive, seen)
        yield ()

      case Term.Let(_, tp, defn, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive, seen)
          _ <- checkPolarity(indName, ctorName, defn, positive, seen)
          _ <- checkPolarity(indName, ctorName, body, positive, seen)
        yield ()

      case Term.Con(_, _, args) =>
        args.foldLeft[Either[String, Unit]](Right(())) { (acc, arg) =>
          acc.flatMap(_ => checkPolarity(indName, ctorName, arg, positive, seen))
        }

      case Term.Mat(s, cases, rt) =>
        for
          _ <- checkPolarity(indName, ctorName, s, positive, seen)
          _ <- checkPolarity(indName, ctorName, rt, positive, seen)
          _ <- cases.foldLeft[Either[String, Unit]](Right(())) { (acc, c) =>
            acc.flatMap(_ => checkPolarity(indName, ctorName, c.body, positive, seen))
          }
        yield ()

      case Term.Fix(_, tp, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive, seen)
          _ <- checkPolarity(indName, ctorName, body, positive, seen)
        yield ()

      // Var, Uni, Meta, Ind(other name) — no occurrence of indName
      case _ => Right(())

  /** Does `dName` use its `argIdx`-th parameter strictly positively in every
   *  constructor? Required when the type being defined occurs at that parameter.
   *
   *  `Eq` is a built-in absent from the environment; its `refl` constructor has
   *  no fields, so its parameters are trivially strictly positive. Any other
   *  inductive that cannot be looked up — including the one being defined
   *  nesting inside its *own* parameters — is rejected conservatively: we
   *  cannot establish positivity for constructors we cannot see.
   */
  private def paramStrictlyPositive(
    dName: String, argIdx: Int, indName: String, ctorName: String,
    seen: Set[(String, Int)],
  )(using env: GlobalEnv): Either[String, Unit] =
    if seen.contains((dName, argIdx)) then Right(())
    else if dName == "Eq" then Right(())
    else env.lookupInd(dName) match
      case None =>
        Left(
          s"Strict positivity violation: '$indName' occurs in an argument of '$dName', " +
          s"whose constructors are not available to check, in constructor '$ctorName'"
        )
      case Some(d) =>
        val p = d.params.length
        val q = d.indices.length
        if argIdx >= p then
          // An index argument. Indices land in constructor return types and can
          // flow anywhere; do not attempt to reason about them.
          Left(
            s"Strict positivity violation: '$indName' occurs in an index argument of '$dName' " +
            s"in constructor '$ctorName'"
          )
        else
          val seen2 = seen + ((dName, argIdx))
          d.ctors.foldLeft[Either[String, Unit]](Right(())) { (acc, c) =>
            acc.flatMap { _ =>
              c.argTpes.zipWithIndex.foldLeft[Either[String, Unit]](Right(())) {
                case (acc2, (argTpe, j)) => acc2.flatMap { _ =>
                  // Inside argTpes(j): Var(0..j-1) are the previous ctor args,
                  // Var(j..j+q-1) the indices (reversed), Var(j+q..j+q+p-1) the
                  // params (reversed). Param argIdx is therefore:
                  val target = j + q + (p - 1 - argIdx)
                  varPositive(dName, c.name, indName, ctorName, argTpe, target,
                              positive = true, seen2)
                }
              }
            }
          }

  /** Check that `Var(target)` occurs only in strictly positive positions in `t`.
   *
   *  The De Bruijn mirror of [[checkPolarity]]: `target` shifts under binders
   *  where a name would not, and an occurrence at another applied inductive's
   *  parameter recurses through [[paramStrictlyPositive]] — a negative use two
   *  inductives deep is still a negative use.
   */
  private def varPositive(
    dName: String, dCtor: String, indName: String, ctorName: String,
    t: Term, target: Int, positive: Boolean, seen: Set[(String, Int)],
  )(using env: GlobalEnv): Either[String, Unit] =
    def bad: Left[String, Unit] = Left(
      s"Strict positivity violation: '$indName' occurs in an argument of '$dName', " +
      s"but '$dName.$dCtor' uses that parameter in a negative position " +
      s"(in constructor '$ctorName')"
    )
    t match
      case Term.Var(k) =>
        if k == target && !positive then bad else Right(())

      case app @ Term.App(_, _) =>
        val (head, args) = peelSpine(app)
        head match
          case Term.Ind(eName, _, _) =>
            args.zipWithIndex.foldLeft[Either[String, Unit]](Right(())) {
              case (acc, (arg, i)) => acc.flatMap { _ =>
                if !Term.freeIn(target, arg) then Right(())
                else if !positive then bad
                else
                  for
                    _ <- varPositive(dName, dCtor, indName, ctorName, arg, target, positive = true, seen)
                    _ <- paramStrictlyPositive(eName, i, indName, ctorName, seen)
                  yield ()
              }
            }
          case _ =>
            for
              _ <- varPositive(dName, dCtor, indName, ctorName, head, target, positive, seen)
              _ <- args.foldLeft[Either[String, Unit]](Right(())) { (acc, a) =>
                     acc.flatMap(_ => varPositive(dName, dCtor, indName, ctorName, a, target, positive, seen))
                   }
            yield ()

      case Term.Pi(_, dom, cod) =>
        for
          _ <- varPositive(dName, dCtor, indName, ctorName, dom, target, !positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, cod, target + 1, positive, seen)
        yield ()

      case Term.Lam(_, tp, body) =>
        for
          _ <- varPositive(dName, dCtor, indName, ctorName, tp, target, positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, body, target + 1, positive, seen)
        yield ()

      case Term.Let(_, tp, defn, body) =>
        for
          _ <- varPositive(dName, dCtor, indName, ctorName, tp, target, positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, defn, target, positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, body, target + 1, positive, seen)
        yield ()

      case Term.Con(_, _, args) =>
        args.foldLeft[Either[String, Unit]](Right(())) { (acc, arg) =>
          acc.flatMap(_ => varPositive(dName, dCtor, indName, ctorName, arg, target, positive, seen))
        }

      case Term.Mat(s, cases, rt) =>
        for
          _ <- varPositive(dName, dCtor, indName, ctorName, s, target, positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, rt, target, positive, seen)
          _ <- cases.foldLeft[Either[String, Unit]](Right(())) { (acc, c) =>
            acc.flatMap(_ =>
              varPositive(dName, dCtor, indName, ctorName, c.body, target + c.bindings, positive, seen))
          }
        yield ()

      case Term.Fix(_, tp, body) =>
        for
          _ <- varPositive(dName, dCtor, indName, ctorName, tp, target, positive, seen)
          _ <- varPositive(dName, dCtor, indName, ctorName, body, target + 1, positive, seen)
        yield ()

      case Term.Uni(_) | Term.Meta(_) | Term.Ind(_, _, _) => Right(())
