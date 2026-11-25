[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# 共通の定義と証明の枠組み

各例の証明に共通する定義と、「ループする族があれば停止しない」という汎用補題を説明します。行の番号は分類ページに合わせて 1 から数えます（Lean のコードは 0 から数えます）。

## 行列と展開

- 列は自然数の有限列、行列は列の有限列です。行列 $`M`$ の最右列を $`C = (c_1, \dots, c_N)`$、$`M`$ から $`C`$ を除いたものを $`M^-`$ と書きます。
- $`t`$ は $`C`$ の非零最下行の番号、つまり $`c_t \gt  0`$ かつ $`y \gt  t \Rightarrow c_y = 0`$ を満たす $`t`$ です。
- bad root $`R = (r_1, \dots, r_N)`$ はルールセットごとの bad root 探索で決まります（[rules.md](rules.md)）。bad part $`B`$ は $`R`$ から $`C`$ の直前の列までです。
- $`\delta_y = c_y - r_y \ (y \lt  t)`$、$`\delta_y = 0 \ (y \ge t)`$ と置きます。上昇フラグ $`a_{xy} \in \lbrace 0, 1\rbrace`$ はルールセットごとの上昇ルールで決まります。
- $`B_k = B + k (A \otimes \Delta)`$、つまり $`B`$ の列 $`x`$、行 $`y`$ に $`k a_{xy} \delta_y`$ を足したものです。
- 展開は $`M[n] = M^- B_1 B_2 \cdots B_n`$ です。$`C`$ が全部 0 のときや bad root がないときは $`M[n] = M^-`$ です。

Lean では `expand R M n`（[Expand.lean](../lean/Common/Expand.lean)）です。展開は最右列以外のすべての列をそのまま残すので、$`M[n]`$ は必ず $`M^-`$ で始まります。$`M[0] = M^-`$ です。

## 計算と「停止しない」

分類ページの計算は、行列とブラケットの組を次のように更新し、行列が空になったら止まります。

```math
(M_0, n_0) = (M, n), \qquad (M_{i+1}, n_{i+1}) = (M_i[f(n_i)], f(n_i))
```

$`\mathrm{Halts}_R(M, n)`$ は「ある $`i`$ で $`M_i`$ が空」という意味です（Lean: `Halts`）。各例で証明するのは $`\forall n \ge 1, \neg \mathrm{Halts}_R(M, n)`$ です。

後で説明する汎用補題は、$`f`$ の形によらず、各段のブラケットが 1 以上であれば成り立ちます。そのため、ブラケットを $`f(n)`$ に変えるのがコピーの前か後か（[rules.md](rules.md) の注 7）は結論に影響しません。

## 標準形

$`\iota_N = (0,\dots,0)(1,\dots,1)`$（$`N`$ 行）と置きます。$`M`$ が標準形であるとは、次が成り立つことです（Lean: `Std`）。

```math
\exists N, \exists n_1, \dots, n_m,\quad \iota_N[n_1][n_2]\cdots[n_m] = \mathrm{pad}_N(M)
```

$`\mathrm{pad}_N(M)`$ は $`M`$ の各列の下に 0 を足して $`N`$ 行にしたものです。BMS では最下行の 0 の行を省いて書くのが慣例です。例えば $`(0,0,0)(1,1,1)(2,1,1)(1,1,1)`$ は、4 行の $`(0,0,0,0)(1,1,1,1)`$ から $`(0,0,0,0)(1,1,1,0)(2,1,1,0)(1,1,1,0)`$ として到達します。

0 の行を足しても展開は変わりません。Lean では、列の長さがそろった行列 $`M`$ について次を証明しています（[Pad.lean](../lean/Common/Pad.lean)）。

```math
\mathrm{pad}_N(M)[n] = \mathrm{pad}_N(M[n]), \qquad \mathrm{Halts}_R(\mathrm{pad}_N(M), n) \iff \mathrm{Halts}_R(M, n)
```

各例の主定理には、0 の行を足した行列についての非停止も含めています。

## 汎用補題: ループする族があれば停止しない

$`Y \sqsubseteq X`$ で「$`Y`$ は $`X`$ の接頭辞」を表します。行列の集合 $`S`$ が次の 2 条件を満たすとします（Lean: `Loop R S 1`）。

1. $`\forall X \in S,\ X \ne ()`$
2. $`\forall X \in S,\ \forall n \ge 1,\ \exists Y \in S,\ Y \sqsubseteq X[n]`$

すると次が成り立ちます（[Loop.lean](../lean/Common/Loop.lean)）。

- (a) `Loop.not_halts`: $`\forall n \ge 1`$ について $`f(n) \ge 1`$ なら、$`\forall X \in S, \forall n \ge 1, \neg \mathrm{Halts}_R(X, n)`$。
- (b) `Loop.not_acc`、`Loop.infinite_descent`: $`S`$ の各元は展開関係について整礎でない。つまり $`X = X_0, X_1, X_2, \dots`$ で、各 $`X_{i+1}`$ が $`X_i`$ のある展開に等しい無限列がある。

**証明のあらまし。** 鍵は「$`Z \ne ()`$ なら $`(Y Z)[n] = Y Z'`$ となる $`Z'`$ がある」ことです。展開は最右列以外を残すからです。$`X \in S`$ から計算を始めると、1 段目は $`X[n] = Y Z`$（$`Y \in S`$）になります。その後の計算は、

- 行列がちょうど $`Y`$ になるか、
- $`Y`$ を真の接頭辞として持ったまま永久に続くか

のどちらかです。後者なら空にならず、前者なら $`Y \in S`$ から同じ議論を繰り返します。これを停止までの段数に関する強い帰納法にまとめると (a) が出ます。(b) は、$`Y Z`$ から $`[0]`$ を繰り返して $`Y`$ に戻ることで、$`S`$ の元を接頭辞に持つ行列からいつでも先に進めることから出ます。

各例の証明は、族 $`S`$ を具体的に定めて条件 2 を示す部分（`Loop.lean`）と、標準形の経路（`Standard.lean`）からなります。

## 検証

- **出典のトレース**（`lean/*/Trace.lean`）: 出典ページに書かれた展開の各行が、定義どおりの展開と一致することを `decide` で確認しています。出典の誤記もここに記録しています。
- **yaBMS との照合**（[Test/YaBMS.lean](../lean/Test/YaBMS.lean)）: BM1.1 と BM2 の標準形の経路とループの族に出てくる 72 個の行列を、ブラケット 1 と 2 で展開しました。144 件すべてが [yaBMS](https://github.com/koteitan/yaBMS) の `-v 1.1` / `-v 2` の出力と一致することを、`decide` で確認しています。テストの生成は [tools/crosscheck.sh](../tools/crosscheck.sh) で行います。
- **公理**（[Test/Axioms.lean](../lean/Test/Axioms.lean)）: 主定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。`sorry` と `native_decide` は使っていません。

## 出典

| 内容 | URL |
|---|---|
| 分類ページ（2023-02-10 版） | [ユーザーブログ:Koteitan/バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E) |
| BM1, BM1.1 の例（hyp cos） | [Talk:Bashicu matrix system](https://googology.fandom.com/wiki/Talk:Bashicu_matrix_system)（"Something wrong happens", "Still with problems"） |
| BM1 の例（Bubby3） | [User blog:Bubby3/BM1 is weaker than expected.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM1_is_weaker_than_expected.) |
| BM2 の例（Bubby3） | [User blog:Bubby3/BM2 doesn't terminate.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM2_doesn%27t_terminate.) |
| BM3 の例（Alemagno12） | [User blog:Alemagno12/BM3 has an infinite loop](https://googology.fandom.com/wiki/User_blog:Alemagno12/BM3_has_an_infinite_loop) |
| BM3 の $`f`$（BASIC の `A=A*A`） | [BashicuHyudora/BASIC言語による巨大数のまとめ (oldid=14878)](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=14878) |
| 照合に使った実装 | [yaBMS](https://github.com/koteitan/yaBMS) |
