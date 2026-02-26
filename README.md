# sproof

**やさしい定理証明系 — A Proof Assistant for Programmers**

Scala 3 で書かれた、プログラマーのための依存型定理証明系。

---

## なぜ sproof？

従来の proof assistant（Coq・Lean・Agda）が一般プログラマーに広まらなかった理由は、型理論の難しさだけではありません。**構文という UI が「プログラマーに使ってもらう気がない」設計**だったことも大きな原因です。

```coq
(* Coq — 初見で読める？ *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.
```

```scala
// sproof — Scala/Java/Rust を知っていれば読める
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// defspec: 仕様を書いて、証明プログラムが型エラーになれば失敗
defspec plus_zero(n: Nat): plus(n, Nat.zero) = n program = {
  by induction n {
    case zero    => trivial
    case succ k ih => simplify [plus, ih]
  }
}
```

sproof が目指すのは「**本質的な難しさだけを残す**」こと。

- **学習コスト = 型理論の概念のみ** — 構文は追加コストにしない
- **ブレース `{ }` で統一** — Java/Rust/Scala を知る人が初見で読める
- **フルスペルの英単語タクティク** — `trivial`, `induction`, `simplify`（暗号略語なし）
- **省略形も提供** — `triv`, `induct`, `simp`（略し方が自明なもののみ）
- **丁寧なエラーメッセージ** — 内部用語ではなく、次のステップを示す

---

## 特徴

| | Coq | Lean 4 | sproof |
|--|-----|--------|--------|
| 実装言語 | OCaml | C++ | **Scala 3** |
| 型理論 | CIC | CIC | **Predicative CIC** |
| 構文 | 数学者向け | 改善されたが独自 | **Scalaライク、ブレース統一** |
| Extraction | OCaml/Haskell | Lean自身 | **Scala 3（デフォルト）** |
| Native バイナリ | なし | なし | **Scala Native 対応** |
| タクティク名 | `rfl`, `intros` | `rfl`, `intro` | **`trivial`, `assume`** |

---

## クイックスタート

```bash
# ビルド
sbt cliJVM/run

# ファイルをチェック
sproof check examples/nat.sproof

# Scala 3 に抽出
sproof extract examples/nat.sproof --output Nat.scala
```

---

## 構文ガイド

### 帰納型

```scala
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

inductive List(A: Type) {
  case nil: List(A)
  case cons(head: A, tail: List(A)): List(A)
}
```

### 関数定義

```scala
// ブロック形式
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// 短い場合は = 式
def id(x: Nat): Nat = x
```

### 仕様定義（defspec）

`defspec` は「仕様を書いて、証明プログラムが型エラーになれば失敗」という設計思想のキーワードです。Curry-Howard 同型対応: **命題 = 型**、**証明 = プログラム**。

```scala
// defspec 名前(引数): 仕様（命題） program = { 証明プログラム }

// 項証明（直接 term を書く）
defspec plus_zero(n: Nat): plus(n, Nat.zero) = n program = {
  match n {
    case Nat.zero    => trivial
    case Nat.succ(k) => congrArg(Nat.succ, plus_zero(k))
  }
}

// タクティク証明（by ブロック）
defspec plus_comm(n m: Nat): plus(n, m) = plus(m, n) program = {
  by induction n {
    case zero    => simplify [plus]
    case succ k ih => simplify [plus, ih]
  }
}
```

`def` との対称性:
```scala
def    foo(n: Nat): Nat    = { ... }   // 関数定義: 型に対してプログラムを与える
defspec bar(n: Nat): P(n)  program = { ... }  // 仕様定義: 命題に対して証明プログラムを与える
```

### タクティク一覧

| タクティク | 省略形 | 意味 |
|-----------|--------|------|
| `trivial` | `triv` | 自明なゴールを閉じる（両辺が等しいなど） |
| `simplify [lemmas]` | `simp` | 補題を使って簡約する |
| `induction x` | `induct x` | `x` の型で帰納法を適用 |
| `assumption x` | `assume x` | 前提 `x` をコンテキストに導入 |
| `apply f` | — | `f` を現在のゴールに適用 |
| `cases x` | — | `x` のコンストラクタでケース分割 |
| `have h : T = proof` | — | ローカル補題を定義 |
| `calc { ... }` | — | 等式の連鎖推論 |
| `ring` | — | 環の等式を自動証明 |
| `sorry` | — | 未完プレースホルダー（警告付き） |

**初心者へ**: まずフルスペル（`trivial`, `induction`, `simplify`）で書いてください。意味がわかってから省略形を使うのが近道です。

### 演算子定義

```scala
operator (x: Nat) + (y: Nat): Nat = plus(x, y)
```

---

## Scala 3 への Extraction

sproof の証明から Scala 3 コードを自動生成できます。命題（証明）は実行時に消去され、計算部分だけが残ります。

```scala
// sproof
def plus(n: Nat, m: Nat): Nat { ... }
defspec plus_comm(n m: Nat): plus(n, m) = plus(m, n) program = { ... }

// 生成された Scala 3
def plus(n: Nat, m: Nat): Nat = ...
def plus_comm(n: Nat, m: Nat): Unit = ()  // 証明は消去
```

---

## Coq との構文対比

| 概念 | Coq | sproof |
|------|-----|--------|
| 帰納型定義 | `Inductive Nat : Set :=` | `inductive Nat {` |
| 関数定義 | `Fixpoint plus ...` | `def plus ...` |
| 仕様定義 | `Theorem plus_zero ...` | `defspec plus_zero ... program = {` |
| 証明開始 | `Proof.` | `program = {` |
| 証明終了 | `Qed.` | `}` |
| 反射律 | `rfl` / `reflexivity` | `trivial` |
| 簡約 | `simpl` / `simp` | `simplify` / `simp` |
| 前提導入 | `intros` | `assume` |
| 帰納法 | `induction n` | `induction n {` |

---

## アーキテクチャ

```
sproof/
├── core/      # Term ADT、De Bruijn 置換、型付けコンテキスト
├── eval/      # NbE（Normalization by Evaluation）
├── checker/   # 双方向型検査（bidirectional type checking）
├── tactic/    # TacticM モナド、組み込みタクティク
├── syntax/    # パーサー（Parsley）、表面AST、pretty-print
├── extract/   # Scala 3 コード生成
├── kernel/    # 信頼済みカーネル（<500行、監査可能）
└── cli/       # REPL、ファイルローダー
```

型理論: **Predicative CIC**（Calculus of Inductive Constructions）
- 宇宙階層: `Type`, `Type1`, `Type2`, ...
- 帰納型 + 不動点（再帰関数）
- Curry-Howard 同型対応（証明 = プログラム）

---

## ライセンス

MIT
