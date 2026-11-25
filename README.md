[English](README-en.md) | [Japanese](README.md)

# 停止しないバシク行列の亜種の形式化

[バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E)（[英語版](https://googology.fandom.com/wiki/User_blog:Koteitan/Categorizing_of_the_rule_sets_for_all_sub_versions_of_bashicu_matrix)）で「停止しない」とされているルールセットについて、挙げられた「停止しない例」が実際に停止しないことを Lean 4 で証明しました。

## 結果

各例について次を証明しています。

1. 例の行列 $`M`$ は、そのルールセットの標準形である。つまり $`(0,\dots,0)(1,\dots,1)`$ から展開で到達できる。
2. 任意の $`n \ge 1`$ について、$`M[n]`$ から始まる計算 $`(M, n) \mapsto (M[f(n)], f(n))`$ は空行列に到達しない。
3. $`M`$ から始まる展開の無限下降列がある。

| ルールセット | 停止しない例 | 出典 | 解説 |
|---|---|---|---|
| BM1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` | hyp cos | [doc/BM1/1](doc/BM1/1/README.md) |
| BM1 | `(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)` | Bubby3 | [doc/BM1/2](doc/BM1/2/README.md) |
| rTSS | BM1 の例 1 と同じ | (BM1 と同じ規則) | [doc/rTSS](doc/rTSS/README.md) |
| BM1.1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` | hyp cos | [doc/BM1.1](doc/BM1.1/README.md) |
| BM2.1 | BM1.1 の例と同じ | (BM1.1 と同じ展開規則) | [doc/BM2.1](doc/BM2.1/README.md) |
| Bubby3's fix | BM1.1 の例と同じ | (BM1.1 と同じ規則) | [doc/Bubby3fix](doc/Bubby3fix/README.md) |
| BM2 | `(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)` | Bubby3 | [doc/BM2](doc/BM2/README.md) |
| BM3 | `(0,0,0)(1,1,1)(2,1,1)(1,1,1)` | Alemagno12 | [doc/BM3](doc/BM3/README.md) |

- 共通の定義、証明の枠組み、出典: [doc/README.md](doc/README.md)
- 分類ページの規則と Lean の定義の対応: [doc/rules.md](doc/rules.md)

分類ページで「壊れている」「停止しないと予想」とだけ書かれているもの（BM3.1、BM3.2、BM3.1.1）と、停止しないとの記述がないもの（BM4、BM2.3、BM2.2）は扱っていません。

## Y 数列の亜種: Bismuth

[Bismuth](https://googology.fandom.com/wiki/User_blog:Syst3ms/Bismuth_:_not_Y_sequence,_but_close)（Syst3ms による Y 数列に似た表記、2019/9/29 版）について、次を証明しました。解説は [doc/1y-bismuth](doc/1y-bismuth/README.md) にあります。

- `(1,2,4,7,5,4,5,10)` は $`(1,3)`$ から展開で到達できる標準形の数列である。
- その展開 $`[n]`$ は、$`1 \le n \le 20`$ のどの $`n`$ でも計算が終わらない。

Bismuth の定義はプログラムそのものなので、プログラムを Lean に書き直して示しています。展開の計算の途中で、表の先頭の行の最後の項が 0 でなくなるまで列を右へ写し続ける手順が呼ばれます。このとき写す列が 1 つもないので、表は変わらず、繰り返しが終わりません。BMS の例のような展開の無限下降列ではなく、1 回の展開の計算そのものが終わらない、という種類の非停止です。

## 証明の方針

各例について、$`M`$ を含む行列の族 $`S`$ を作り、次を示します。

```math
\forall X \in S,\ \forall n \ge 1,\ \exists Y \in S,\ Y \sqsubseteq X[n]
```

（$`\sqsubseteq`$ は接頭辞を表します）

展開は最右列以外の列を残すので、計算は $`Y`$ にちょうど戻るか、$`Y`$ を接頭辞に持ったまま永久に続くかのどちらかです。このことから停止しないことが従います（[doc/README.md](doc/README.md)）。

定義が分類ページの意図どおりであることは、次の 2 つで確かめています。

- 出典に書かれた展開のトレースを `decide` で再現する。
- BM1.1 と BM2 について、[yaBMS](https://github.com/koteitan/yaBMS) の出力 144 件と一致することを確かめる。

## ビルド

[elan](https://github.com/leanprover/elan) で Lean 4（v4.33.1）を入れてから、次を実行します。Mathlib は使っていません。

```sh
cd lean
lake build
```

`lake build` は、全定理と、出典のトレース・yaBMS との照合のテストを検証します。主定理が使う公理は `lean/Test/Axioms.lean` で確認できます（`propext`, `Classical.choice`, `Quot.sound` のみ）。

## ディレクトリ構成

```
lean/
  Common/            共通の定義と補題
    Matrix.lean        行列, 非零最下行, Δ, 0 の行の補完
    BadRoot.lean       bad root 探索 (左隣法, 上行枝無視方式)
    Ascend.lean        bad part 上昇ルール (全枝有効, BM2 方式, BM3 方式)
    Expand.lean        展開, 計算, 停止, 標準形
    Rules.lean         7 つのルールセット
    Loop.lean          汎用補題: ループする族があれば停止しない
    Lemmas.lean        展開の計算のための補題
    Ubim.lean          上行枝無視方式の親・先祖の補題
    Pad.lean           0 の行を足しても展開が変わらないこと
  BM1/1/ BM1/2/ BM1.1/ BM2/ BM3/
    Standard.lean      標準形の経路
    Loop.lean          ループする族
    Trace.lean         出典のトレースの再現
    Main.lean          主定理
  rTSS/ BM2.1/ Bubby3fix/
    Main.lean          系
  1y-bismuth/        Bismuth (2019/9/29 版)
    Model.lean         プログラムの Lean への書き直し
    Decide.lean        上限なしで計算して無限ループを見つける関数と、その正しさ
    Standard.lean      標準形であることの確認
    Main.lean          主定理
  Test/              yaBMS との照合, 公理の確認
  Explore/           探索用の #eval (ビルド対象外)
doc/                 証明の解説 (日本語 README.md, 英語 README-en.md)
tools/               yaBMS との照合テストの生成, Bismuth の差分テスト
```
