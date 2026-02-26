package sproof.core

/** De Bruijn index-based term representation for predicative CIC. */
enum Term:
  // λ計算の基本構成素
  case Var(idx: Int)                                               // De Bruijn index (0-based)
  case App(fn: Term, arg: Term)                                    // 関数適用
  case Lam(name: String, tpe: Term, body: Term)                   // λ抽象
  case Pi(name: String, dom: Term, cod: Term)                     // 依存関数型 (∀x:A. B)
  case Let(name: String, tpe: Term, defn: Term, body: Term)       // let束縛

  // 宇宙
  case Uni(level: Int)                                             // Type_0, Type_1, ...

  // 帰納型
  case Ind(name: String, params: List[Param], ctors: List[Ctor])  // 帰納型定義
  case Con(name: String, indRef: String, args: List[Term])        // コンストラクタ適用
  case Mat(scrutinee: Term, cases: List[MatchCase], returnTpe: Term) // パターンマッチ

  // 再帰
  case Fix(name: String, tpe: Term, body: Term)                   // 不動点演算子

  // エラボレーション用メタ変数
  case Meta(id: Int)

  def show: String = Term.show(this)

object Term:
  def show(t: Term, ctx: List[String] = Nil): String = t match
    case Var(i)            => ctx.lift(i).getOrElse(s"#$i")
    case App(f, a)         => s"(${show(f, ctx)} ${show(a, ctx)})"
    case Lam(x, tp, b)    => s"(λ$x:${show(tp, ctx)}. ${show(b, x :: ctx)})"
    case Pi(x, d, c)      =>
      if freeIn(0, c) then s"(∀$x:${show(d, ctx)}. ${show(c, x :: ctx)})"
      else s"(${show(d, ctx)} → ${show(c, x :: ctx)})"
    case Let(x, tp, df, b) =>
      s"(let $x:${show(tp, ctx)} = ${show(df, ctx)} in ${show(b, x :: ctx)})"
    case Uni(l)            => if l == 0 then "Type" else s"Type$l"
    case Ind(n, _, _)      => n
    case Con(n, _, _)      => n
    case Mat(s, _, _)      => s"(match ${show(s, ctx)} { ... })"
    case Fix(n, _, _)      => s"(fix $n)"
    case Meta(i)           => s"?$i"

  /** Check if De Bruijn index `idx` occurs free in term `t` (used for arrow-type detection). */
  def freeIn(idx: Int, t: Term): Boolean = t match
    case Var(i)           => i == idx
    case App(f, a)        => freeIn(idx, f) || freeIn(idx, a)
    case Lam(_, tp, b)   => freeIn(idx, tp) || freeIn(idx + 1, b)
    case Pi(_, d, c)     => freeIn(idx, d) || freeIn(idx + 1, c)
    case Let(_, tp, df, b) => freeIn(idx, tp) || freeIn(idx, df) || freeIn(idx + 1, b)
    case Uni(_)           => false
    case Con(_, _, args)  => args.exists(freeIn(idx, _))
    case Mat(s, cs, rt)  =>
      freeIn(idx, s) || freeIn(idx, rt) ||
      cs.exists(c => freeIn(idx + c.bindings, c.body))
    case Ind(_, ps, cs)  =>
      ps.exists(p => freeIn(idx, p.tpe)) || cs.exists(c => freeIn(idx, c.tpe))
    case Fix(_, tp, b)   => freeIn(idx, tp) || freeIn(idx + 1, b)
    case Meta(_)          => false

/** Parameter declaration (name: type). */
case class Param(name: String, tpe: Term)

/** Constructor declaration (name: type). */
case class Ctor(name: String, tpe: Term)

/** One case in a match expression. */
case class MatchCase(ctor: String, bindings: Int, body: Term)
