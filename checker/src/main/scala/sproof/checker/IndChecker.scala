package sproof.checker

import sproof.core.{Term, Context, Subst, GlobalEnv, IndDef, CtorDef, MatchCase}

/** Type-checking rules for inductive types: constructors (Con) and eliminators (Mat).
 *
 *  This module is NOT part of the trusted kernel.
 *  Every proof term it produces is re-checked by `Kernel.check`.
 *
 *  Design note: both methods take `using env: GlobalEnv` as a contextual parameter
 *  so they can look up constructor types and inductive definitions.
 */
object IndChecker:

  // ---- Con: constructor type inference ----

  /** Infer the type of a constructor application `Con(name, indRef, args)`.
   *
   *  Returns `Ind(indRef, ...)` if all argument types check out.
   */
  def inferCon(
    ctx:    Context,
    name:   String,
    indRef: String,
    args:   List[Term],
  )(using env: GlobalEnv): Either[TypeError, Term] =
    env.lookupInd(indRef) match
      case None =>
        Left(TypeError.Custom(s"Unknown inductive type '$indRef'"))
      case Some(indDef) =>
        indDef.ctors.find(_.name == name) match
          case None =>
            Left(TypeError.Custom(s"Unknown constructor '$name' for inductive type '$indRef'"))
          case Some(ctorDef) =>
            if args.length != ctorDef.argTpes.length then
              Left(TypeError.Custom(
                s"Constructor '$name' expects ${ctorDef.argTpes.length} argument(s), " +
                s"got ${args.length}"
              ))
            else
              checkArgs(ctx, args, ctorDef.argTpes).map { _ =>
                // The type of any constructor is the inductive type itself
                Term.Ind(indRef, indDef.params, Nil)
              }

  // ---- Mat: match expression type checking ----

  /** Check a match expression `Mat(scrutinee, cases, returnTpe)`.
   *
   *  - Infers the type of the scrutinee and looks up its inductive definition.
   *  - Verifies that the cases are exactly the constructors of that type (exhaustive).
   *  - Checks each case body against `returnTpe` in the appropriately extended context.
   *  - Returns `returnTpe` as the overall type.
   */
  def checkMat(
    ctx:       Context,
    scrutinee: Term,
    cases:     List[MatchCase],
    returnTpe: Term,
  )(using env: GlobalEnv): Either[TypeError, Term] =
    for
      scrutTpe <- Bidirectional.infer(ctx, scrutinee)
      // NOTE: do NOT call whnf here — Eval.eval converts Ind(...) to a neutral SNeu(NVar(-1), Nil),
      // destroying the inductive type name.  Use the raw inferred type directly.
      indName  <- extractIndName(scrutTpe)
      indDef   <- env.lookupInd(indName).toRight(
                    TypeError.Custom(s"Unknown inductive type '$indName'")
                  )
      _        <- checkCoverage(cases, indDef)
      _        <- checkCases(ctx, cases, indDef, returnTpe)
    yield returnTpe

  // ---- private helpers ----

  /** Check each argument against its expected type (pairwise). */
  private def checkArgs(
    ctx:  Context,
    args: List[Term],
    tpes: List[Term],
  )(using env: GlobalEnv): Either[TypeError, Unit] =
    args.zip(tpes).foldLeft[Either[TypeError, Unit]](Right(())) { case (acc, (arg, tpe)) =>
      acc.flatMap(_ => Bidirectional.check(ctx, arg, tpe))
    }

  /** Extract the inductive type name from a (possibly normalized) type term. */
  private def extractIndName(t: Term): Either[TypeError, String] = t match
    case Term.Ind(name, _, _) => Right(name)
    case _ => Left(TypeError.Custom(
      s"Scrutinee must have an inductive type; got: ${t.show}"
    ))

  /** Verify that the match cases cover exactly the constructors (no missing, no extra). */
  private def checkCoverage(
    cases:  List[MatchCase],
    indDef: IndDef,
  ): Either[TypeError, Unit] =
    val ctorNames = indDef.ctors.map(_.name).toSet
    val caseNames = cases.map(_.ctor).toSet
    val missing   = ctorNames -- caseNames
    val extra     = caseNames -- ctorNames
    if missing.isEmpty && extra.isEmpty then Right(())
    else
      val msgs = List(
        Option.when(missing.nonEmpty)(s"missing: ${missing.mkString(", ")}"),
        Option.when(extra.nonEmpty)(s"unexpected: ${extra.mkString(", ")}"),
      ).flatten
      Left(TypeError.Custom(
        s"Non-exhaustive match for '${indDef.name}': ${msgs.mkString("; ")}"
      ))

  /** Check the body of each match case against `returnTpe`. */
  private def checkCases(
    ctx:       Context,
    cases:     List[MatchCase],
    indDef:    IndDef,
    returnTpe: Term,
  )(using env: GlobalEnv): Either[TypeError, Unit] =
    cases.foldLeft[Either[TypeError, Unit]](Right(())) { case (acc, mc) =>
      acc.flatMap { _ =>
        indDef.ctors.find(_.name == mc.ctor) match
          case None =>
            Left(TypeError.Custom(s"Unknown constructor '${mc.ctor}' in match"))
          case Some(ctorDef) =>
            if mc.bindings != ctorDef.argTpes.length then
              Left(TypeError.Custom(
                s"Case '${mc.ctor}' declares ${mc.bindings} binding(s) " +
                s"but constructor has ${ctorDef.argTpes.length} argument(s)"
              ))
            else
              // Extend context with constructor argument bindings.
              // foldLeft prepends each arg type; last arg in argTpes → Var(0).
              val extCtx = ctorDef.argTpes.foldLeft(ctx) { (c, argTpe) =>
                c.extend("_", argTpe)
              }
              // Shift returnTpe so free variables remain valid in the extended context.
              val shiftedRetTpe = Subst.shift(mc.bindings, returnTpe)
              Bidirectional.check(extCtx, mc.body, shiftedRetTpe)
      }
    }
