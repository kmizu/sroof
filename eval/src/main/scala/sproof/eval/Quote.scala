package sproof.eval

import sproof.core.{Term, Param, Ctor, MatchCase}

/** Quote a semantic value back to a Term (read-back phase of NbE).
 *
 *  `size` = current context depth (= next available De Bruijn level).
 *  Fresh variables are SNeu(NVar(level)); quoted as Var(size - level - 1).
 */
object Quote:
  def quote(size: Int, s: Semantic): Term = s match
    case Semantic.SLam(x, tpe, body) =>
      val v    = Semantic.freshVar(size)
      Term.Lam(x, quote(size, tpe), quote(size + 1, body(v)))

    case Semantic.SPi(x, dom, cod) =>
      val v    = Semantic.freshVar(size)
      Term.Pi(x, quote(size, dom), quote(size + 1, cod(v)))

    case Semantic.SUni(l) =>
      Term.Uni(l)

    case Semantic.SCon(name, ref, args) =>
      Term.Con(name, ref, args.map(quote(size, _)))

    case Semantic.SNeu(head, spine) =>
      spine.foldLeft(quoteNeutral(size, head))((acc, arg) =>
        Term.App(acc, quote(size, arg)))

  private def quoteNeutral(size: Int, n: Neutral): Term = n match
    case Neutral.NVar(level) =>
      Term.Var(size - level - 1)  // convert De Bruijn level → index

    case Neutral.NApp(fn, arg) =>
      Term.App(quoteNeutral(size, fn), quote(size, arg))

    case Neutral.NMat(scrut, cases, _) =>
      val scrutTerm = quoteNeutral(size, scrut)
      val caseTerms = cases.map { nc =>
        val freshVars = (0 until nc.bindings).toList.map(i => Semantic.freshVar(size + i))
        val bodyVal   = nc.body(freshVars)
        MatchCase(nc.ctor, nc.bindings, quote(size + nc.bindings, bodyVal))
      }
      Term.Mat(scrutTerm, caseTerms, Term.Uni(0))

    case Neutral.NFix(name, body, arg) =>
      val v = Semantic.freshVar(size)
      Term.App(
        Term.Fix(name, Term.Uni(0), quote(size + 1, body(v))),
        quoteNeutral(size, arg),
      )

  /** Normalize a term: eval then quote. */
  def normalize(size: Int, env: Env, t: Term): Term =
    quote(size, Eval.eval(env, t))

  /** Definitional equality: compare normal forms. */
  def convEqual(size: Int, env: Env, t1: Term, t2: Term): Boolean =
    alphaEq(quote(size, Eval.eval(env, t1)), quote(size, Eval.eval(env, t2)))

  /** Alpha-equality (syntactic equality modulo binder names). */
  def alphaEq(t1: Term, t2: Term): Boolean = (t1, t2) match
    case (Term.Var(i), Term.Var(j))                        => i == j
    case (Term.App(f1, a1), Term.App(f2, a2))              => alphaEq(f1, f2) && alphaEq(a1, a2)
    case (Term.Lam(_, tp1, b1), Term.Lam(_, tp2, b2))     => alphaEq(tp1, tp2) && alphaEq(b1, b2)
    case (Term.Pi(_, d1, c1), Term.Pi(_, d2, c2))          => alphaEq(d1, d2) && alphaEq(c1, c2)
    case (Term.Let(_, tp1, df1, b1), Term.Let(_, tp2, df2, b2)) =>
      alphaEq(tp1, tp2) && alphaEq(df1, df2) && alphaEq(b1, b2)
    case (Term.Uni(l1), Term.Uni(l2))                      => l1 == l2
    case (Term.Con(n1, r1, as1), Term.Con(n2, r2, as2))    =>
      n1 == n2 && r1 == r2 && as1.length == as2.length &&
      as1.zip(as2).forall(alphaEq(_, _))
    case (Term.Meta(i), Term.Meta(j))                      => i == j
    case _                                                  => false
