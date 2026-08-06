package sroof.checker

import sroof.core.{Term, Context, Subst, GlobalEnv, IndDef, CtorDef, MatchCase, Param, Ctor}

/** Type-checking rules for inductive types: constructors (Con) and eliminators (Mat).
 *
 *  This module IS inside the trusted computing base for logical validity.
 *  `Kernel.verify` delegates to `Bidirectional.check`, which calls straight into
 *  the rules below — so "the kernel re-checks it" does not apply here: the kernel
 *  re-checks *using* this code. A bug here is a valid proof of the wrong
 *  statement, and nothing downstream can catch it.
 *
 *  (This comment previously claimed the opposite. The v0.10.0 constructor-index
 *  unsoundness lived here for seven releases, accepted by the kernel every time.)
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
            else if isIndexed(indDef) then
              val p = indDef.params.length
              val q = indDef.indices.length
              // The heuristic below can only recover a value that appears *directly* as
              // some argument's type, so it learns nothing from a nullary constructor
              // like `vnil`.  Widening its window to p+q is still necessary: in an
              // indexed family the indices sit between the ctor args and the params, so
              // a p-wide window mislabels every parameter slot.  The index half is then
              // overwritten by values derived from the declaration rather than guessed.
              val spine = extractParamValsFromArgs(indDef, ctorDef, args, ctx, p + q)
              for
                _       <- checkArgsDependent(ctx, args, ctorDef.argTpes, spine)
                idxVals <- ctorIndexValues(indDef, ctorDef, args, spine)
              yield
                (spine.take(p) ++ idxVals)
                  .foldLeft(Term.Ind(indRef, Nil, Nil): Term)(Term.App.apply)
            else
              // Infer param values from arg types (heuristic: works for m=0 and simple m=1 cases)
              val paramVals = extractParamValsFromArgs(indDef, ctorDef, args, ctx, indDef.params.length)
              checkArgsDependent(ctx, args, ctorDef.argTpes, paramVals).map { _ =>
                // Return type: Ind applied to inferred param values
                paramVals.foldLeft(Term.Ind(indRef, Nil, Nil): Term)(Term.App.apply)
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
      result   <- extractEq(scrutTpe) match
                    case Some((_, lhs, rhs)) =>
                      // J-rule: Eq elimination.  returnTpe is the motive function P.
                      // Overall type = App(P, rhs).  Branch body checked against App(P, lhs).
                      checkEqElim(ctx, lhs, rhs, cases, returnTpe)
                    case None =>
                      for
                        indName <- extractIndName(scrutTpe)
                        indDef  <- env.lookupInd(indName).toRight(
                                     TypeError.Custom(s"Unknown inductive type '$indName'")
                                   )
                        _       <- checkCoverage(cases, indDef)
                        _       <- checkCases(ctx, scrutinee, scrutTpe, cases, indDef, returnTpe)
                      yield returnTpe
    yield result

  // ---- public helpers for Bidirectional ----

  /** Extract param values from an expected type that is `App(...App(Ind(indRef), p0)..., pN)`.
   *  Returns Nil if the expected type does not match, or if m=0.
   */
  def extractParamsFromExpected(t: Term, indRef: String): List[Term] =
    def peelApps(t: Term, acc: List[Term]): (Term, List[Term]) = t match
      case Term.App(fn, arg) => peelApps(fn, arg :: acc)
      case _                 => (t, acc)
    val (head, params) = peelApps(t, Nil)
    head match
      case Term.Ind(name, _, _) if name == indRef => params
      case _                                      => Nil

  /** Infer constructor type with explicitly provided param values (check mode support).
   *  Used when the expected type reveals the param values (e.g. expected = List(Nat)).
   */
  def inferConWithParams(
    ctx:       Context,
    name:      String,
    indRef:    String,
    args:      List[Term],
    paramVals: List[Term],
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
            else if isIndexed(indDef) then
              val p = indDef.params.length
              val q = indDef.indices.length
              if paramVals.length != p + q then
                Left(TypeError.Custom(
                  s"'$indRef' takes $p parameter(s) and $q index(es), but the expected " +
                  s"type supplies ${paramVals.length} argument(s)"
                ))
              else
                for
                  _       <- checkArgsDependent(ctx, args, ctorDef.argTpes, paramVals)
                  idxVals <- ctorIndexValues(indDef, ctorDef, args, paramVals)
                yield
                  // Parameters are read off the expected type, as for any parameterised
                  // inductive.  The indices are *derived* from the constructor's own
                  // declaration and deliberately NOT taken from the expected type — that
                  // is the whole point.  Echoing them back would make the caller's
                  // `convCheck` compare the expected type with itself, which is what
                  // let a length-0 `vnil` pass as a length-1 `Vec` before v0.10.
                  (paramVals.take(p) ++ idxVals)
                    .foldLeft(Term.Ind(indRef, Nil, Nil): Term)(Term.App.apply)
            else
              checkArgsDependent(ctx, args, ctorDef.argTpes, paramVals).map { _ =>
                // Return type: Ind applied to param values
                paramVals.foldLeft(Term.Ind(indRef, Nil, Nil): Term)(Term.App.apply)
              }

  // ---- indexed families ----

  /** True when this inductive both declares indices *and* states them on every
   *  constructor.
   *
   *  Both halves matter.  A declaration written before indexed return types were
   *  expressible has `indices` populated but `retIndices = Nil` everywhere — that is
   *  the state of `stdlib/Vec.sroof` — and there is nothing to derive an index from,
   *  so it must keep behaving exactly as it did.  Requiring *all* constructors to
   *  state their indices also means a half-annotated declaration is treated as
   *  un-indexed rather than silently deriving `Nil` for the annotated ones.
   */
  private def isIndexed(indDef: IndDef): Boolean =
    indDef.indices.nonEmpty &&
    indDef.ctors.forall(_.retIndices.length == indDef.indices.length)

  /** The index values of `ctorDef`'s return type, instantiated at this application's
   *  arguments and the family's parameter values.
   *
   *  `retIndices` is elaborated in the scope the *last* argument type sees, so it uses
   *  the same progressive De Bruijn convention `instantiateArgType` already decodes,
   *  with `j = args.length`.  `spine` must therefore be the full parameter-then-index
   *  list (length p+q) in declaration order — which is exactly what
   *  `extractParamsFromExpected` peels off an applied indexed type.
   *
   *  A return index that mentions one of the family's *own* index variables is
   *  rejected.  `case vnil: Vec(A)(n)` would make the derived index equal whatever
   *  the caller expected, so `convCheck` would compare the expected type with itself
   *  and accept anything — the same vacuity this release exists to remove.
   */
  private def ctorIndexValues(
    indDef:  IndDef,
    ctorDef: CtorDef,
    args:    List[Term],
    spine:   List[Term],
  ): Either[TypeError, List[Term]] =
    val n = args.length
    val q = indDef.indices.length
    ctorDef.retIndices.zipWithIndex.find { case (t, _) =>
      (n until n + q).exists(i => Term.freeIn(i, t))
    } match
      case Some((t, k)) =>
        Left(TypeError.Custom(
          s"Constructor '${ctorDef.name}' of '${indDef.name}': return index #${k + 1} " +
          s"(${t.show}) mentions one of '${indDef.name}'s own index variables. " +
          s"A constructor's index must be built from its arguments and the type's parameters."
        ))
      case None =>
        Right(ctorDef.retIndices.map(t => instantiateArgType(t, args, spine)))

  // ---- private helpers ----

  /** Check constructor args with dependent type support.
   *
   *  The argTpes use the progressive De Bruijn convention:
   *    argTpes(j) has nameEnv = [arg_{j-1}, ..., arg_0, param_{m-1}, ..., param_0]
   *  So Var(0..j-1) = prev ctor args, Var(j..j+m-1) = type params.
   *
   *  For each arg at position j, calls `instantiateArgType` which performs a single-pass
   *  simultaneous substitution: prev ctor args and param values are all substituted at once,
   *  avoiding the index-shifting bugs that arise from sequential subst calls.
   */
  private def checkArgsDependent(
    ctx:       Context,
    args:      List[Term],
    argTpes:   List[Term],
    paramVals: List[Term],
  )(using env: GlobalEnv): Either[TypeError, Unit] =
    args.zip(argTpes).zipWithIndex.foldLeft[Either[TypeError, Unit]](Right(())) {
      case (acc, ((arg, rawTpe), j)) =>
        acc.flatMap { _ =>
          val tpe = instantiateArgType(rawTpe, args.take(j), paramVals)
          Bidirectional.check(ctx, arg, tpe)
        }
    }

  /** Simultaneously substitute prev ctor args and param values into a raw argTpe.
   *
   *  In `rawTpe` (elaborated with progressive nameEnv):
   *    Var(k) for k < j   → prev ctor arg args(k)   (k=0 is the most recent prev arg)
   *    Var(k) for k in [j, j+m) → paramVals(m-1-(k-j))  (Var(j) = last param, Var(j+m-1) = first)
   *
   *  Uses a single recursive traversal to avoid index-shifting errors from sequential subst.
   *  Under `depth` binders, the substituted values are shifted up by `depth`.
   */
  private def instantiateArgType(rawTpe: Term, prevArgs: List[Term], paramVals: List[Term]): Term =
    val j = prevArgs.length
    val m = paramVals.length
    def go(depth: Int, t: Term): Term = t match
      case Term.Var(i) =>
        val abs = i - depth
        if abs < 0 then t  // bound by a binder inside rawTpe
        // `prevArgs` is in declaration order, but the elaborator prepends each
        // argument name to the scope, so Var(0) is the *most recent* one.  The
        // index therefore counts backwards from the end.
        else if abs < j then Subst.shift(depth, prevArgs(j - 1 - abs))
        else if abs < j + m then
          val paramIdx = m - 1 - (abs - j)
          Subst.shift(depth, paramVals(paramIdx))
        else t  // free var beyond ctor args and params (shouldn't appear in well-formed argTpe)
      case Term.App(f, a)          => Term.App(go(depth, f), go(depth, a))
      case Term.Lam(x, tp, b)     => Term.Lam(x, go(depth, tp), go(depth + 1, b))
      case Term.Pi(x, d, c)       => Term.Pi(x, go(depth, d), go(depth + 1, c))
      case Term.Let(x, tp, df, b) => Term.Let(x, go(depth, tp), go(depth, df), go(depth + 1, b))
      case Term.Uni(_)             => t
      case Term.Meta(_)            => t
      case Term.Ind(nm, ps, cs)   =>
        Term.Ind(nm,
          ps.map(p => Param(p.name, go(depth, p.tpe))),
          cs.map(c => Ctor(c.name, go(depth, c.tpe))))
      case Term.Con(nm, r, as)    => Term.Con(nm, r, as.map(go(depth, _)))
      case Term.Fix(nm, tp, b)    => Term.Fix(nm, go(depth, tp), go(depth + 1, b))
      case Term.Mat(s, cases, rt) =>
        Term.Mat(
          go(depth, s),
          cases.map(mc => mc.copy(body = go(depth + mc.bindings, mc.body))),
          go(depth, rt),
        )
    go(0, rawTpe)

  /** Build the instantiated ctor arg type for position j in the extended context.
   *
   *  In `checkCases`, after extending ctx with j ctor args (at Var(0..j-1)),
   *  the param values from the outer ctx need to be shifted by j.
   *  This replaces param vars Var(j..j+m-1) in rawTpe with shift(j, paramVals[k]).
   */
  def instantiateCtorArgTpe(rawTpe: Term, j: Int, paramVals: List[Term]): Term =
    val m = paramVals.length
    if m == 0 then rawTpe  // non-parameterized: argTpe is already correct in ext ctx
    else
      def go(depth: Int, t: Term): Term = t match
        case Term.Var(i) =>
          val absI = i - depth
          if absI >= j && absI < j + m then
            // This is param at position m-1-(absI-j) from start
            val paramIdx = m - 1 - (absI - j)
            Subst.shift(depth + j, paramVals(paramIdx))
          else
            Term.Var(i)
        case Term.App(f, a)          => Term.App(go(depth, f), go(depth, a))
        case Term.Lam(x, tp, b)     => Term.Lam(x, go(depth, tp), go(depth + 1, b))
        case Term.Pi(x, d, c)       => Term.Pi(x, go(depth, d), go(depth + 1, c))
        case Term.Let(x, tp, df, b) => Term.Let(x, go(depth, tp), go(depth, df), go(depth + 1, b))
        case Term.Uni(_)             => t
        case Term.Meta(_)            => t
        case Term.Ind(nm, ps, cs)   =>
          Term.Ind(nm,
            ps.map(p => Param(p.name, go(depth, p.tpe))),
            cs.map(c => Ctor(c.name, go(depth, c.tpe))))
        case Term.Con(nm, r, as)    => Term.Con(nm, r, as.map(go(depth, _)))
        case Term.Fix(nm, tp, b)    => Term.Fix(nm, go(depth, tp), go(depth + 1, b))
        case Term.Mat(s, cases, rt) =>
          Term.Mat(
            go(depth, s),
            cases.map(mc => mc.copy(body = go(depth + mc.bindings, mc.body))),
            go(depth, rt),
          )
      go(0, rawTpe)

  /** Extract the inductive type name from a (possibly App-wrapped) type term. */
  private def extractIndName(t: Term): Either[TypeError, String] = t match
    case Term.Ind(name, _, _) => Right(name)
    case Term.App(fn, _)      => extractIndName(fn)
    case _ => Left(TypeError.Custom(
      s"Scrutinee must have an inductive type; got: ${t.show}"
    ))

  /** Extract type parameter values from `App(App(Ind(name), p0), p1, ...)`.
   *  Returns Nil for non-parameterized types. */
  def extractIndParams(t: Term): List[Term] =
    def peel(t: Term, acc: List[Term]): List[Term] = t match
      case Term.App(fn, arg) => peel(fn, arg :: acc)
      case _                 => acc
    peel(t, Nil)

  /** Infer param values from constructor arg types (heuristic for infer mode).
   *
   *  For each slot k, finds the first argTpe(j) that is exactly Var(j+window-1-k)
   *  (i.e., directly the k-th entry), and uses the inferred type of the corresponding arg.
   *  Returns Uni(0) for slots that cannot be extracted (fallback).
   *
   *  `window` is the number of De Bruijn slots the declaration's binders occupy beyond
   *  the constructor's own arguments: `params.length` for an ordinary inductive, and
   *  `params.length + indices.length` for an indexed family, where the indices sit
   *  between the arguments and the parameters.  Passing the wrong width does not just
   *  lose information — it reads a parameter out of an index's slot.
   */
  private def extractParamValsFromArgs(
    indDef:  IndDef,
    ctorDef: CtorDef,
    args:    List[Term],
    ctx:     Context,
    window:  Int,
  )(using env: GlobalEnv): List[Term] =
    if window == 0 then Nil
    else
      val paramVals = Array.fill[Term](window)(Term.Uni(0))
      ctorDef.argTpes.zipWithIndex.foreach { (rawTpe, j) =>
        rawTpe match
          case Term.Var(i) if i >= j && i < j + window =>
            val paramIdx = window - 1 - (i - j)
            args.lift(j).foreach { arg =>
              Bidirectional.infer(ctx, arg) match
                case Right(argType) => paramVals(paramIdx) = argType
                case Left(_)        => ()
            }
          case _ => ()
      }
      paramVals.toList

  /** Extract (tpe, lhs, rhs) from an Eq type term (2-arg or 3-arg form). */
  private def extractEq(t: Term): Option[(Term, Term, Term)] = t match
    case Term.App(Term.App(Term.App(Term.Ind("Eq", _, _), tpe), lhs), rhs) =>
      Some((tpe, lhs, rhs))
    case Term.App(Term.App(Term.Ind("Eq", _, _), lhs), rhs) =>
      Some((Term.Meta(-1), lhs, rhs))
    case _ =>
      None

  /** Check a J-rule (Eq elimination) match.
   *
   *  `Mat(scrutinee, [MatchCase("refl", 1, body)], motiveFunc)`
   *  where `scrutinee : Eq T lhs rhs` and `motiveFunc : T → Type`.
   *
   *  - Branch body is checked against `App(motiveFunc, lhs)` (shifted for the refl witness).
   *  - Overall type returned is `App(motiveFunc, rhs)`.
   */
  private def checkEqElim(
    ctx:       Context,
    lhs:       Term,
    rhs:       Term,
    cases:     List[MatchCase],
    motiveFunc: Term,
  )(using env: GlobalEnv): Either[TypeError, Term] =
    if cases.length != 1 || cases.head.ctor != "refl" || cases.head.bindings != 1 then
      Left(TypeError.Custom(
        s"J-rule (Eq elimination) match must have exactly one 'refl' case with 1 binding; " +
        s"got cases: ${cases.map(c => s"${c.ctor}/${c.bindings}").mkString(", ")}"
      ))
    else
      val body = cases.head.body
      for
        lhsTpe       <- Bidirectional.infer(ctx, lhs)
        branchCtx     = ctx.extend("x", lhsTpe)
        // Branch body type = App(motiveFunc, lhs) shifted for the refl witness binder
        branchBodyTpe = Subst.shift(1, Term.App(motiveFunc, lhs))
        _            <- Bidirectional.check(branchCtx, body, branchBodyTpe)
      yield Term.App(motiveFunc, rhs)

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

  /** Check the body of each match case against `returnTpe`.
   *
   *  @param scrutinee the original scrutinee term (used to specialize returnTpe)
   *  @param scrutTpe  the inferred type of the scrutinee (used to extract param values)
   */
  private def checkCases(
    ctx:       Context,
    scrutinee: Term,
    scrutTpe:  Term,
    cases:     List[MatchCase],
    indDef:    IndDef,
    returnTpe: Term,
  )(using env: GlobalEnv): Either[TypeError, Unit] =
    // Extract type param values from the scrutinee's type.
    // e.g. scrutTpe = App(Ind("PolyList"), Nat) → paramVals = [Nat]
    val paramVals = extractIndParams(scrutTpe)
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
              val n = ctorDef.argTpes.length
              // Extend context with constructor argument bindings.
              // For each arg at position j (0-indexed from left), instantiate its type:
              // - substitute param values (shifted by j for the j already-added args)
              // - Var(0..j-1) in argTpes(j) are the prev ctor args, already correct in ext ctx
              val (extCtx, _) = ctorDef.argTpes.zipWithIndex.foldLeft((ctx, 0)) {
                case ((c, j), (rawTpe, _)) =>
                  val instantiated = instantiateCtorArgTpe(rawTpe, j, paramVals)
                  (c.extend("_", instantiated), j + 1)
              }
              // Build the constructor application term in the extended context.
              // Ctor args are Var(n-1)..Var(0) (most recent = Var(0)).
              val ctorApp = Term.Con(ctorDef.name, indDef.name,
                (0 until n).toList.map(i => Term.Var(n - 1 - i)))
              // Specialize returnTpe for this constructor:
              //   replace Var(scrutineeIdx) with ctorApp, shift all other free vars by n.
              // If scrutinee is not a Var, fall back to plain shift (conservative).
              val specializedRetTpe = scrutinee match
                case Term.Var(k) => specializeForCase(returnTpe, k, ctorApp, n)
                case _           => Subst.shift(n, returnTpe)
              Bidirectional.check(extCtx, mc.body, specializedRetTpe)
      }
    }

  /** Specialize `returnTpe` for a match case branch.
   *
   *  Replaces `Var(varIdx)` (the scrutinee) with `ctorApp` (the constructor
   *  application in the extended context) and shifts all other free variables by `n`
   *  (to account for the `n` new constructor-arg bindings).
   *
   *  Unlike `specializeGoal` in Builtins, this does NOT remove the old binding;
   *  it only shifts other free variables up by `n`.
   */
  private def specializeForCase(t: Term, varIdx: Int, ctorApp: Term, n: Int): Term =
    import sroof.core.{Param, Ctor}
    def go(depth: Int, t: Term): Term = t match
      case Term.Var(i) =>
        val absI = i - depth
        if absI < 0 then Term.Var(i)                           // bound inside depth binders
        else if absI == varIdx then Subst.shift(depth, ctorApp) // replace scrutinee
        else Term.Var(i + n)                                    // other free vars: shift +n
      case Term.App(f, a)          => Term.App(go(depth, f), go(depth, a))
      case Term.Lam(x, tp, b)     => Term.Lam(x, go(depth, tp), go(depth + 1, b))
      case Term.Pi(x, d, c)       => Term.Pi(x, go(depth, d), go(depth + 1, c))
      case Term.Let(x, tp, df, b) => Term.Let(x, go(depth, tp), go(depth, df), go(depth + 1, b))
      case Term.Uni(_)             => t
      case Term.Meta(_)            => t
      case Term.Ind(nm, ps, cs)   =>
        Term.Ind(nm,
          ps.map(p => Param(p.name, go(depth, p.tpe))),
          cs.map(c => Ctor(c.name, go(depth, c.tpe))))
      case Term.Con(nm, r, args)  => Term.Con(nm, r, args.map(go(depth, _)))
      case Term.Fix(nm, tp, b)    => Term.Fix(nm, go(depth, tp), go(depth + 1, b))
      case Term.Mat(s, cases, rt) =>
        Term.Mat(
          go(depth, s),
          cases.map(mc => mc.copy(body = go(depth + mc.bindings, mc.body))),
          go(depth, rt),
        )
    go(0, t)
