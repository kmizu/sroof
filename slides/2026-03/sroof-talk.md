---
marp: true
theme: default
paginate: true
style: |
  section {
    font-family: 'Noto Sans JP', 'Helvetica Neue', sans-serif;
    font-size: 26px;
    background: #ffffff;
    color: #1a1a2e;
    padding: 50px 60px 40px;
  }
  h1 {
    color: #16213e;
    border-bottom: 3px solid #e94560;
    padding-bottom: 10px;
    margin-bottom: 24px;
    font-size: 1.4em;
  }
  h2 {
    color: #0f3460;
    font-size: 1.1em;
  }
  code, pre {
    background: #f4f4f8;
    border-radius: 6px;
    font-size: 0.78em;
  }
  pre {
    border-left: 4px solid #e94560;
    padding: 12px 16px;
    margin: 12px 0;
  }
  ul, ol {
    margin: 12px 0;
    line-height: 1.8;
  }
  p {
    margin: 10px 0;
    line-height: 1.7;
  }
  table {
    font-size: 0.85em;
    width: 100%;
    border-collapse: collapse;
  }
  th {
    background: #16213e;
    color: white;
    padding: 8px 12px;
  }
  td {
    padding: 7px 12px;
    border-bottom: 1px solid #ddd;
  }
  blockquote {
    border-left: 4px solid #e94560;
    padding: 8px 16px;
    background: #fff8f8;
    margin: 12px 0;
    font-size: 0.9em;
  }
  section.title {
    background: linear-gradient(135deg, #16213e 0%, #0f3460 60%, #1a1a2e 100%);
    color: #ffffff;
    text-align: center;
    justify-content: center;
  }
  section.title h1 {
    color: #e94560;
    border: none;
    font-size: 1.8em;
    line-height: 1.4;
  }
  section.title p {
    color: #ccccdd;
    font-size: 1em;
    margin: 6px 0;
  }
---

<!-- _class: title -->

# Scala専用定理証明支援系<br>sroof

**設計と実装の裏側**

kmizu（水島宏太）
nextbeat / Japan Scala Association

<!--
自己紹介は手短に。
「今日は自分がスクラッチで作った定理証明支援系 sroof の、実装の中身を紹介します」
くらいで入る。
-->

---

# はじめに：おことわり

- 定理証明支援系については**素人**です
- sroof は Claude Code と一緒に作りながら勉強中
- Lean の書籍を読みながら概念をキャッチアップしている最中

**ミステイクや誤解があれば、ぜひ遠慮なく指摘してください！**

> 「作りながら学ぶ」スタイルなので、
> 実装と理論が噛み合っていない部分があるかもしれません

<!--
「定理証明系の専門家ではなく、実装しながら勉強してきた立場で話します。
間違いがあれば会場でもSNSでも気軽に指摘してもらえると嬉しいです。」
-->

---

# 今日話すこと（15分）

1. **定理証明支援系とは？** — プログラムの正しさを数学的に保証するツール
2. **sroof の全体像** — なぜ Scala 構文？
3. **依存型** — 型で仕様を書く
4. **De Bruijn インデックス** — 変数束縛の実装方法
5. **NbE（Normalization by Evaluation）** — 「等しい」をどう判定するか
6. **型検査アルゴリズム** — 型を推論・検証する仕組み
7. **タクティックとカーネル** — 証明を生成して検証する

<!--
「前半は What（何を作ったか）、後半は How（どう実装したか）という構成です。
型システムの知識がなくても大丈夫なように話します。」
-->

---

# 定理証明支援系とは？

**「このコードは正しい」をコンピュータに証明させるツール**

```scala
// ← これは「仕様」を型として書いている
defspec add_assoc(a b c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
  by induction a { ... }  // ← これが「証明」
}
```

- 型検査を通る = 証明が正しい（コンパイラが確認してくれる）
- テストは「いくつかの入力で動く」を確認するだけ
- 定理証明は「すべての入力で正しい」を数学的に証明する

> Lean 4, Coq, Agda, Idris などが有名。sroof はその仲間。

<!--
「テストとの違いを強調する。テストは有限個の入力を試すだけ。
定理証明は数学的に『全ての入力で正しい』を保証する。
コードの上の行が『仕様』で、中身が『証明』というのがポイント。」
-->

---

# なぜ sroof を作ったのか

既存の定理証明支援系の問題：

| 問題 | 例 |
|------|-----|
| Scala/Java 開発者に馴染みのない構文 | Lean や Coq は独自構文 |
| 独自エコシステムを一から学ぶ必要がある | ライブラリも全部別物 |
| 実装が複雑で「中で何が起きてるか」わからない | Lean は 100 万行超 |

**sroof のアプローチ：**
- **Scala 風ブレース構文** → Scala 開発者がすぐ読める
- **Scala 3 でスクラッチ実装** → 実装を理解できる規模
- **シンプルな信頼カーネル** → コアロジックは 500 行以下

<!--
「Lean 4 は素晴らしいシステムだが、実装は 100 万行超で全体像を把握するのが難しい。
sroof は『Scala 開発者がちょっと試してみる』ハードルを下げることを目指した。
実装も追えるサイズを意識している。」
-->

---

# sroof 言語の見た目

```scala
// データ型の定義（ほぼScalaと同じ見た目）
inductive Nat {
  case zero: Nat
  case succ(n: Nat): Nat
}

// 関数定義
def plus(n: Nat, m: Nat): Nat {
  match n {
    case Nat.zero    => m
    case Nat.succ(k) => Nat.succ(plus(k, m))
  }
}

// 定理 + 証明
defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
  by induction n {
    case zero      => trivial
    case succ k ih => simplify [ih]
  }
}
```

<!--
「Scala を書いたことがあれば、だいたい読めると思います。
inductive がデータ型定義、defspec が定理の定義。
by induction というのが証明戦略で、trivial は『計算すれば明らか』という意味。」
-->

---

# アーキテクチャ全体像

```
.sroof ファイル（人間が書くもの）
       ↓
    Parser  ─── 構文解析
       ↓
   SurfaceAst  ─── 表面的な構文木
       ↓
   Elaborator  ─── 内部表現に変換（★後で詳しく）
       ↓
   core Term   ─── 機械が扱う内部表現
       ↓
  Checker Phase 1  ─── タクティック実行（証明候補を生成）
       ↓
  Kernel.verify   ─── 証明が本当に正しいか確認（★信頼境界）
       ↓
    検証済み証明 ✓
```

<!--
「★印の2か所が今日のキモ。
Elaborator は人間の書いた構文を機械向けに変換する層。
Kernel.verify が最後に証明を独立して再確認する、信頼の砦。
この2つを軸に話を進めます。」
-->

---

# Elaborator とは？

**「人間が読みやすい構文」を「機械が処理しやすい形」に変換する**

Scala の typer フェーズに近い概念。ただし、依存型があると話が複雑：

- 型を決めるために値を評価する必要がある
- 値を評価するために型が必要
- この「鶏と卵」の問題を解くのが Elaboration

**Elaborator が変換するもの：**

| 人間が書くもの | 内部表現 |
|--------------|---------|
| 名前付き変数 `n` | De Bruijn インデックス `Var(1)` |
| `structure { field: T }` | inductive + アクセサ関数 |
| `a + b` | `__opr_plus(a, b)` |
| 型省略箇所 | メタ変数 `Meta(?)` |

<!--
「一般的なコンパイラだと型チェックと脱糖は別々の処理として書けるが、
依存型だと型と値が相互依存するので一体的に処理する必要がある。
この複雑な変換プロセスをまとめて Elaboration と呼ぶ。定理証明系特有の用語。」
-->

---

# 依存型とは？

**「型の中に値を含められる」型システム**

普通の型：
```scala
// List[A] ── 要素の型は分かるが、長さの情報はない
val xs: List[Int] = List(1, 2, 3)  // 長さ3でも100でも同じ型
```

依存型：
```scala
// Vec(A, n) ── 長さ n が型に含まれる！
val xs: Vec(Int, 3) = ...  // 「長さ3のIntリスト」が型レベルで保証される
```

**何が嬉しいか：**
- 「長さ0のリストの先頭要素を取る」がコンパイルエラーになる
- 「ソートした結果と元のリストの長さが同じ」を型で表現できる
- **バグの可能性を型レベルで排除できる**

<!--
「Scala だと List[Int] は長さの情報を持たない。
Vec(Int, 3) は長さ 3 という情報が型に含まれているので、
型検査を通るだけで長さに関するバグが防げる。
これが sroof で扱いたい世界観。」
-->

---

# 依存型の例：長さ付きリスト

```scala
inductive Vec(A: Type, n: Nat) {
  case vnil: Vec(A, Nat.zero)               // 空リスト（長さ0）
  case vcons(head: A, k: Nat,
             tail: Vec(A, k)): Vec(A, Nat.succ(k))  // 先頭+残り（長さk+1）
}

// 先頭要素を取る関数 ── 長さ0のVecは型レベルで渡せない！
def head(A: Type, n: Nat, xs: Vec(A, Nat.succ(n))): A {
  match xs {
    case Vec.vcons(h k t) => h
    // vnil のケースは書かなくていい（型が合わないから）
  }
}
```

`Vec(A, Nat.succ(n))` という型が「長さ1以上」を保証している

<!--
「引数の型が Vec(A, Nat.succ(n)) なので、長さ0の vnil は渡せない。
コンパイラが弾いてくれる。
パターンマッチも vnil のケースを書かなくてよくて、網羅性も型が保証する。」
-->

---

# 内部表現：Term ADT

Elaborator が変換した後の内部表現はこの 11 ケース：

```scala
enum Term:
  case Var(idx: Int)                               // 変数（De Bruijn番号）
  case App(fn: Term, arg: Term)                    // 関数適用
  case Lam(name: String, tpe: Term, body: Term)   // λ抽象（関数定義）
  case Pi(name: String, dom: Term, cod: Term)     // 依存関数型
  case Let(name: String, tpe: Term, defn: Term, body: Term)
  case Uni(level: Int)                             // Type₀, Type₁, ...
  case Ind(...)   // 帰納型定義
  case Con(...)   // コンストラクタ
  case Mat(...)   // パターンマッチ
  case Fix(...)   // 再帰関数
  case Meta(id: Int)                               // 未確定の型穴
```

すべての sroof プログラムは最終的にこの形で扱われる

<!--
「型検査も証明の生成も、全部この11種類の木を操作するだけ。
Var が変数、Lam が関数定義、Pi が依存型、Fix が再帰。
シンプルな表現に落とし込むことで、型検査器やカーネルの実装がシンプルになる。」
-->

---

# De Bruijn インデックスとは？

**変数名の代わりに「何個上の λ で束縛されたか」という番号を使う**

```
名前あり：  λx. λy. x + y
De Bruijn： λ.  λ.  1 + 0
                    ↑   ↑
              1個上のλ  直近のλ
```

**なぜ番号を使うのか？**

- **α変換が不要** — `λx.x` と `λy.y` は同じ意味だが名前が違う
  → De Bruijn では両方とも `λ. 0` で同一
- **代入の実装が機械的に正しくできる**
- 変数キャプチャの問題が自動的に回避できる

変数の「名前」は型検査や証明には関係ない。
番号だけが本質。

<!--
「0が一番近いλ、1がその外のλ。番号が距離を表している。
名前を使わないのでリネームが不要で、内部処理がすっきりする。
Coqもこの方式。実装者には鉄板の選択肢。」
-->

---

# De Bruijn：代入するとき何が起きるか

`plus(n, m)` の `n` に `Nat.zero` を代入するとき：

```
コンテキスト: [m, n]  ← インデックス 0=m, 1=n

plus(Var(1), Var(0))   // plus(n, m)
     ↑
  n = Var(1) を Nat.zero に置換

→ plus(Nat.zero, Var(0))  // plus(Nat.zero, m)
```

**λの中に入るとき、インデックスをずらす必要がある：**

```
λx. Var(1)   ← Var(1) は λ の外の変数を指してる
     ↓ λ の中でさらに変数を代入するとき
     +1 してずらす（シフト）
```

> このシフト操作のバグが sroof で最も多いバグ源

<!--
「λをくぐるたびに番号がずれる。これを補正するのがシフト操作。
ここのオフバイワンが一番よくやるバグ。
特に帰納法のタクティック実装でこのシフトを手書きするので、慎重になる必要がある。」
-->

---

# NbE（Normalization by Evaluation）

**「等しい」をどうやって判定するか？**

```
plus(Nat.zero, n)   と   n   ── これは等しい？
```

構文的には全然違う木。でも計算すれば同じになる。

**NbE のアプローチ：**
```
両辺を「実行」して正規形にする → 同じ構造になれば等しい

plus(Nat.zero, n)  →[実行]→  n  ← 正規形
n                  →[実行]→  n  ← 正規形

同じ！ → 等しい ✓
```

**定義的等価性（definitional equality）** と呼ぶ。
型検査の核心部分で常に使われる。

<!--
「型検査で『この型とこの型は同じか？』を判定するときに常に使う。
単純に文字列比較すると plus(Nat.zero, n) と n は別物に見える。
でも計算してみると同じになる。この『計算して比べる』がNbEの基本アイデア。」
-->

---

# NbE：なぜ「評価して戻す」のか

**NbE は定理証明系全般で使われる標準的な実装手法**
Lean 4（C++）、Agda（OCaml）、Coq（OCaml）も同じアプローチ。sroof では Scala のクロージャを活用する。

**直接 Term を書き換えて正規化しようとすると：**
- 変数が出てきたとき「ここで止まる」を自分で管理する必要がある
- 展開するたびに De Bruijn のシフト・代入を手で計算し直す → バグりやすい

**NbE なら実装言語のクロージャに任せられる：**
```
Term ──[Eval]──→ Semantic（実装言語のクロージャ）
              ──[Quote]──→ Term（正規形）
```

- **Eval**：β簡約 = 関数呼び出しになる → シフト・代入のコード不要
- **Quote**：変数（行き詰まり）はそのまま残すだけ

<!--
「NbEはLean、Agda、Coqも使っている定石。
sroof固有の工夫ではなく、定理証明系の標準的な実装手法。
実装言語のクロージャを使うことで、変数束縛の管理を実装言語のランタイムに任せられる。」
-->

---

# 型検査：双方向型推論

型を「合成」するモードと「確認」するモードの2種類：

```
推論モード（⇒）：この式の型は何か？  → 型を返す
検査モード（⇐）：この式は型 T か？   → OK か エラー
```

**実装のイメージ：**
```scala
def infer(ctx, term): Type = term match
  case Var(i)    => ctx.lookup(i)           // コンテキストから型を取得
  case App(f, a) =>
    val Pi(_, dom, cod) = infer(ctx, f)     // 関数の型を推論
    check(ctx, a, dom)                      // 引数を確認
    cod(a)                                  // 返り型（依存型なので引数を代入）

def check(ctx, term, expected): Unit = term match
  case Lam(n, _, b) =>                      // λ式は Pi 型に対して確認
    val Pi(_, dom, cod) = expected
    check(ctx.extend(n, dom), b, cod)
  case _ =>                                 // それ以外は推論して比較
    val actual = infer(ctx, term)
    assert(nbeEqual(actual, expected))      // NbE で等価性を確認
```

<!--
「infer は型を返す、check は型が合ってるか確認するだけ。
この2モードを使い分けることで型注釈の省略が実現できる。
最後の nbeEqual が先ほどの NbE で、ここで定義的等価性を使う。」
-->

---

# タクティックシステム

**ユーザーは「証明の戦略」を高レベルで書く → タクティックが内部 Term を生成**

```scala
defspec plus_succ(n m: Nat): plus(n, Nat.succ(m)) = Nat.succ(plus(n, m)) {
  by induction n {
    case zero      => trivial       // 計算で自明
    case succ k ih => simplify [ih] // 帰納法仮定 ih を使う
  }
}
```

| タクティック | 生成する内部 Term |
|-------------|-----------------|
| `trivial` | `refl`（両辺が計算で等しいとき） |
| `induction n` | `Fix(λn. Mat(n, [...]))` |
| `simplify [ih]` | ih で書き換えた後の `refl` |
| `assumption h` | `Var(h のインデックス)` |

<!--
「induction や trivial はユーザーが書く高レベルな言葉。
その裏では Fix や Mat といった内部 Term を組み立てている。
タクティックはあくまで proof term の『生成器』で、それ自体は信頼されていない。」
-->

---

# カーネル：信頼境界

**タクティックが生成した証明を、独立して再検証する**

```
  タクティック（信頼しない）
       ↓ proof term を生成
  Kernel.verify（これだけ正しければ健全）
       ↓ 通過すれば証明成立
```

**なぜ分離するのか：**

タクティックにバグがあっても、カーネルが正しければ健全性は保たれる

```scala
// Phase 1: タクティック実行（信頼しない）
val candidates = generateProofCandidates(elabResult)

// Phase 2: カーネルで全件再検証（これが唯一の真実）
candidates.foreach(c => Kernel.verify(ctx, c.proofTerm, c.proposition))
```

カーネルは **500 行以下**。読んで理解できる規模を意識している。

<!--
「これが sroof の設計で一番大事な部分。
タクティックに何かバグがあっても、カーネルを通らない限り証明として認められない。
カーネルだけ正しければシステム全体の健全性が保たれる。
500行なので、自分で読んで検証できるサイズにしている。」
-->

---

# 証明エージェント（おまけ）

**`by sorry` を自動で正しいタクティックに置き換える**

```
sroof agent examples/nat.sroof
```

**BFS 探索の戦略：**

```
Depth 0 — まず簡単なものを試す
  trivial, assumption, simplify[], decide, ...

Depth 1 — 構造帰納法を試す
  induction n { case zero => ... ; case succ k ih => ... }
  induction n generalizing m { ... }  // 変数を汎化
```

スコア順に試して、最初に成功したタクティックで
ソースファイルを自動書き換え！

<!--
「sorry は証明を一時的にスキップするプレースホルダー。
エージェントは BFS でタクティック候補を探索して、
うまくいったものでソースを書き換えてくれる。
簡単な定理なら自動で証明できる。」
-->

---

# まとめ

| 技術 | 役割 |
|------|------|
| **De Bruijn インデックス** | 変数を番号で管理、α変換不要 |
| **NbE** | 「実行して戻す」で定義的等価性を判定 |
| **双方向型検査** | 推論と確認の 2 モードで型を扱う |
| **タクティックモナド** | 証明状態を純粋関数的に管理 |
| **信頼カーネル** | タクティックと独立して証明を再検証 |

これらを **Scala 3 でスクラッチ実装** → 実装を追える規模感

**[github.com/kmizu/sroof](https://github.com/kmizu/sroof)**

<!--
「定理証明系というと難しそうに聞こえるが、
De Bruijn、NbE、双方向型検査、カーネルの4つの概念を押さえれば
基本的な実装は理解できる。
興味があればぜひ実装を読んでみてください。PRも歓迎です！」
-->

---

<!-- _class: title -->

# ご清聴ありがとうございました！

**Q&A**

[github.com/kmizu/sroof](https://github.com/kmizu/sroof)

@kmizu

> 「型検査を通ればバグはない…かもしれない」

<!--
質問が来そうなトピック：
- 「Lean や Agda との違いは？」→ 構文の馴染みやすさと実装の読みやすさが違い
- 「パフォーマンスは？」→ 今は小さいプログラム向け、最適化は今後
- 「実用的に使えるか？」→ まだ研究・学習目的がメイン、stdlib は充実してきてる
- 「証明エージェントはどこまで自動化できる？」→ 帰納法1段階まで。複雑な証明はまだ手書き
-->
