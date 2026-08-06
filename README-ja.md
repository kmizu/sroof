# sroof

**やさしい定理証明系 — プログラマーのための Proof Assistant**

sroof は Scala 3 で書かれた依存型定理証明系です。Scala・Java・Rust・C++ を知っているプログラマーが、形式的検証を自然に書けることを目指しています。

[![CI](https://github.com/kmizu/sroof/actions/workflows/ci.yml/badge.svg)](https://github.com/kmizu/sroof/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

---

## なぜ sroof？

従来の証明支援系（Coq・Lean・Agda）が一般プログラマーに広まらなかった原因は、依存型の難しさだけではありません。**構文という UI が「プログラマーに使ってもらう気がない」設計**だったことも大きな原因です。

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
// sroof — Scala/Java/Rust を知っていれば初見で読める
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// defspec: 仕様（命題）に対して証明プログラムを与える
defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

sroof が目指すのは「**本質的な難しさだけを残す**」こと。

- **学習コスト = 型理論の概念のみ** — 構文は追加コストにしない
- **ブレース `{ }` で統一** — Java/Rust/Scala を知る人が初見で読める
- **フルスペルの英単語タクティク** — `trivial`, `induction`, `simplify`（暗号略語なし）
- **省略形も提供** — `triv`, `induct`, `simp`（自明に略せるものだけ）
- **丁寧なエラーメッセージ** — 内部用語ではなく、次のステップを示す

---

## 比較表

|                | Coq             | Lean 4         | sroof                        |
|----------------|-----------------|----------------|-------------------------------|
| 実装言語        | OCaml           | C++            | **Scala 3**                   |
| 型理論          | CIC             | CIC            | **Predicative CIC**           |
| 構文            | 数学者向け       | 改善されたが独自 | **Scala ライク、ブレース統一** |
| Extraction 先   | OCaml / Haskell | Lean 自身       | **Scala 3（デフォルト）**     |
| Native バイナリ | —               | —              | **Scala Native 対応**         |
| 反射律タクティク | `rfl`           | `rfl`          | **`trivial`**                 |
| 前提導入        | `intros`        | `intro`        | **`assume`**                  |

---

## クイックスタート

```bash
# クローン & ビルド
git clone https://github.com/kmizu/sroof
cd sroof
sbt cli/run

# 証明ファイルを検査
sbt "cli/run check examples/nat.sroof"
```

### 出力例

```
OK: examples/nat.sroof — 1 inductive(s), 1 definition(s), 4 defspec(s)
```

### v0.3 リリース情報

- 変更履歴: [`CHANGELOG.md`](CHANGELOG.md)
- リリースノート: [`RELEASE_NOTES_v0.3.md`](RELEASE_NOTES_v0.3.md)
- リリースチェックリスト: [`RELEASE_CHECKLIST_v0.3.md`](RELEASE_CHECKLIST_v0.3.md)

### 移行メモ（v0.2 → v0.3）

- **壊れるものはありません。** `.sroof` 言語、CLI、stdlib、examples、VS Code 拡張、
  sbt プラグイン、ネイティブバイナリはすべて v0.2 と同じ挙動です。
- Scala 3 フロントエンドは加算的です。コンパイラプラグインを有効にしなければ、
  ビルドは一切影響を受けません。
- Scala 経路では信頼モデルに主張がひとつ増えました。依拠する前に
  [`docs/trust-model.md`](docs/trust-model.md) を確認してください。
- ドキュメントの誤り訂正: タクティク表に載っていた `ring` と省略形 `induct` は
  どちらも実装に存在しません。また `assumption` と `assume` は別のタクティクです。
  ネイティブバイナリ名は `sroof-cli-native` です（`-out` は付きません）。

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

inductive Bool {
  case true:  Bool
  case false: Bool
}
```

### 関数定義

```scala
// ブロック形式（再帰関数）
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// 式形式（短い場合）
def id(x: Nat): Nat = x
```

### 仕様定義（defspec）

`defspec` は Curry-Howard 同型対応を直接表現するキーワードです。
**命題 = 型**、**証明 = プログラム**。

```
defspec 名前(引数): 命題 { 証明プログラム }
```

`def` との対称性：

```scala
def     foo(n: Nat): Nat  =         { n }         // 関数: 型に対してプログラム
defspec bar(n: Nat): P(n) { ... }       // 仕様: 命題に対して証明プログラム
```

証明プログラムが間違った型を持つ場合は型エラーとして弾かれます。普通のコードの型エラーと同じ扱いです。

### タクティク証明

```scala
// trivial: 両辺が定義的に等しい場合
defspec plus_zero_left(m: Nat): plus(Nat.zero, m) = m {
  by trivial
}

// 帰納法と帰納仮説（IH）
defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

### 項証明（Curry-Howard 項を直接書く）

```scala
defspec refl_intro(n: Nat): n = n {
  by induction n {
    case zero   => trivial
    case succ k => trivial
  }
}
```

---

## タクティク一覧

### ゴールを閉じる

| タクティク      | 省略形         | 意味                                             |
|----------------|---------------|--------------------------------------------------|
| `trivial`      | `triv`, `rfl` | 両辺が定義的に等しければゴールを閉じる             |
| `decide`       | —             | 決定可能なゴールを閉じる（現状は `trivial` と同じ）|
| `assumption`   | —             | コンテキストにある仮定でゴールを閉じる             |
| `contradiction`| —             | 矛盾した仮定から任意のゴールを閉じる               |
| `tauto`        | —             | 命題論理のトートロジーを消化する                   |
| `exact e`      | —             | 明示的な証明項 `e` でゴールを閉じる                |
| `sorry`        | —             | 未完プレースホルダー（不健全・警告付き）           |
| `skip`         | —             | 何もしない                                        |

### 書き換えと場合分け

| タクティク                             | 省略形    | 意味                                                    |
|---------------------------------------|----------|---------------------------------------------------------|
| `simplify [f, g, ...]`                | `simp`   | 指定した補題で簡約して閉じる。省略時は `@[simp]` 集合を使用 |
| `rewrite [h]`                         | `rw [h]` | 与えた等式でゴールを書き換える                            |
| `induction x { ... }`                 | —        | `x` の型でコンストラクタ分割。再帰ケースに IH 付き        |
| `induction x generalizing y z { ... }`| —        | 上記に加え、IH を `y`, `z` について全称量化する           |
| `cases x { ... }`                     | —        | 帰納仮説なしでコンストラクタ分割                          |

### 構造と論理

| タクティク                   | 省略形             | 意味                                          |
|-----------------------------|-------------------|-----------------------------------------------|
| `assume x ...`              | `intro`, `intros` | `∀` 束縛変数をコンテキストに導入する            |
| `apply f`                   | —                 | `f` の戻り型でゴールを縮約し、引数をサブゴールに |
| `have h : T = { p }; rest`  | —                 | ローカル補題を定義してから `rest` を続ける       |
| `calc { ... }`              | —                 | 等式の連鎖推論                                  |
| `split` / `constructor`     | —                 | 連言を分割 / 唯一のコンストラクタを適用          |
| `left` / `right`            | —                 | 選言の第1 / 第2コンストラクタを選ぶ              |
| `use e`                     | `exists e`        | 存在量化子に証拠を与える                         |
| `obtain [x y] from h`       | —                 | 仮定を分解する                                   |
| `specialize h arg`          | —                 | 全称量化された仮定を具体化する                   |
| `by_contra h`               | —                 | 背理法。否定を `h` として仮定する                |

### コンビネータ

| 形                    | 意味                                     |
|----------------------|------------------------------------------|
| `{ t1; t2; t3 }`     | 順に実行する                              |
| `try t`              | `t` を試し、失敗しても成功扱いにする        |
| `first \| t1 \| t2`  | 最初に成功した選択肢を採用する              |
| `repeat t`           | 進展がなくなるまで `t` を繰り返す           |
| `all_goals t`        | 残る全ゴールに `t` を適用する               |

**simp ルール修飾子**: `simplify` に渡す補題名には接尾辞が付けられる。
`h__rev` は逆向き書き換え、`h__p10` は優先度を上げる（大きいほど先に試す）、
`h__rev__p10` は両方。

**初心者へ**: まずフルスペル（`trivial`, `induction`, `simplify`）で書いてください。意味が直感的にわかります。省略形は慣れてから使えば十分です。

---

## Coq との構文対比

| 概念         | Coq                        | sroof                              |
|-------------|----------------------------|-------------------------------------|
| 帰納型定義   | `Inductive Nat : Set :=`   | `inductive Nat {`                   |
| 関数定義     | `Fixpoint plus ...`        | `def plus ...`                      |
| 定理         | `Theorem plus_zero ...`    | `defspec plus_zero ... {` |
| 証明開始     | `Proof.`                   | `{`                                 |
| 証明終了     | `Qed.`                     | `}`                                 |
| 反射律       | `reflexivity` / `rfl`      | `trivial`                           |
| 簡約         | `simpl` / `simp`           | `simplify` / `simp`                 |
| 前提導入     | `intros`                   | `assume`                            |
| 帰納法       | `induction n`              | `induction n {`                     |

---

## Scala 3 への Extraction

```bash
sbt "cli/run extract examples/nat.sroof --output Nat.scala"
```

命題（証明）は実行時に消去され、計算部分だけが Scala 3 コードとして出力されます。

```scala
// sroof
def plus(n: Nat, m: Nat): Nat { ... }
defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n { ... }

// 生成された Scala 3
def plus(n: Nat, m: Nat): Nat = ...
def plus_zero_right(n: Nat): Unit = ()   // 証明は消去
```

---

## 通常の Scala 3 を検証する（初期サブセット）

`.sroof` ファイルを書く代わりに、**普通の Scala** を書いて、sroof コンパイラ
プラグインにコンパイル時に定理を証明させることもできます。

```scala
import sroof.annotation.*
import sroof.lang.*

@proofModule
object NatProofs:

  enum Nat:
    case Zero
    case Succ(n: Nat)

  import Nat.*

  def plus(n: Nat, m: Nat): Nat =
    n match
      case Zero    => m
      case Succ(k) => Succ(plus(k, m))

  @theorem
  def plusZeroRight(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )
```

このファイルは Scala 自身のパーサーと型検査器が処理します。`Nat` と `plus` は
実プログラムのままで、sroof コアから再生成されるわけではありません。プラグインが
加えるのは、`plusZeroRight` がコンパイル時に証明され、`.sroof` 経路と同じ信頼済み
カーネルで再検査されるという一点だけです。定理が成り立たなくなれば、そのファイルは
コンパイルできなくなります。

**これは初期サブセットであり、Scala 全般の検証ではありません。** 現時点で対応して
いるのは、ジェネリックでない enum、それらの上の単一パラメータリストの純粋な `def`、
停止性検査を通る自己再帰、網羅的な match、不変なローカル `val`、等式ゴール、そして
`trivial` / `induction` / `ih` / `simplify` のタクティクです。それ以外（`var`、副作用、
例外、キャスト、クロージャ、ジェネリクス、相互再帰、モジュール外呼び出しなど）は
**近似せずに診断メッセージ付きで拒否**します。

検証はビルドがプラグインを有効にしたときにだけ行われます。アノテーション単体では
何も起こりません。

```scala
Compile / scalacOptions += "-Xplugin:" + pluginClasspath   // build.sbt を参照
```

対応・非対応サブセットの詳細と変換規則は
[docs/scala3-frontend.md](docs/scala3-frontend.md) にあります。動く例は
`examples-scala3/` です。

---

## アーキテクチャ

```
sroof/
├── core/            # Term ADT、De Bruijn 置換、型付けコンテキスト
├── eval/            # NbE（Normalization by Evaluation）
├── checker/         # 双方向型検査（bidirectional type checking）
├── tactic/          # TacticM モナド、組み込みタクティク
├── syntax/          # Parsley ベースパーサー、表面 AST、pretty-print（レガシー .sroof 経路）
├── extract/         # Scala 3 コード生成                              （レガシー .sroof 経路）
├── kernel/          # 信頼済みカーネル（< 500 行、監査可能）
├── cli/             # REPL、ファイルローダー                          （レガシー .sroof 経路）
├── scala-api/       # @proofModule / @theorem アノテーションと sroof.lang DSL
├── scala-frontend/  # 解決済み IR、Scala→コア変換、証明ランナー、カーネルゲート
├── scala-plugin/    # Scala 3 コンパイラプラグイン（コンパイラバージョン固有）
├── examples-scala3/ # プラグインを有効にしてコンパイルされる実 .scala ソース
└── scala-it/        # 実際に dotc を起動する統合テスト
```

**信頼モデルの注意:** Scala 経路では、カーネルが論理的妥当性を判定するのは
`.sroof` 経路とまったく同じですが、追加でひとつ信頼するものがあります —
「コアのモデルが Scala プログラムそのものである」という対応関係です。これは変換層に
依存するため、Scala コードについて述べる定理においては TCB の一部になります。
詳細は [docs/trust-model.md](docs/trust-model.md) を参照してください。

**型理論**: Predicative CIC（Calculus of Inductive Constructions）
- 宇宙階層: `Type`, `Type1`, `Type2`, ...
- 帰納型 + 不動点（再帰関数）
- Curry-Howard 同型対応（証明 = プログラム）

---

## Scala Native（ネイティブバイナリ）

sroof は [Scala Native](https://scala-native.org/) 経由で自己完結型のネイティブバイナリにコンパイルできます。実行時に JVM が不要になります。

### 前提条件

```bash
# Ubuntu / WSL2
sudo apt-get install clang lld libunwind-dev
```

### ビルド

```bash
# 全モジュールを native コンパイルしてリンク
sbt cliNative/nativeLink

# 生成されたネイティブバイナリを実行
./cli-native/target/scala-3.3.6/sroof-cli-native check examples/nat.sroof
```

### 設定

```
nativeLink     : releaseFast + LTO.thin + immix GC（デフォルト）
                 リンクが速く、日常的な開発に向く
releaseFull    : より積極的な最適化（リンクが遅い）→ リリース時に切り替える
```

### LLVM なしでコンパイルだけ確認

```bash
# clang がなくてもコンパイルは通せる
sbt cliNative/compile
```

---

## sbt プラグイン

sbt ビルドへの組み込みは [sbt-sroof](sbt-sroof/README.md) を参照してください。

```sbt
// project/plugins.sbt
addSbtPlugin("io.sroof" % "sbt-sroof" % "0.1.0")

// build.sbt
enablePlugins(SroofPlugin)
```

```bash
sbt sroofCheck    # すべての .sroof ファイルを型検査
sbt sroofExtract  # Scala 3 ソースへ抽出（コンパイル前に自動実行）
sbt sroofRepl     # 対話的 REPL を起動
```

---

## ライセンス

MIT
