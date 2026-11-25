[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Common definitions and the proof framework

This page explains the definitions shared by all the proofs, and the general lemma "a looping family implies non-termination". Rows are numbered from 1 as on the classification page (the Lean code numbers them from 0).

## Matrices and expansion

- A column is a finite sequence of natural numbers, and a matrix is a finite sequence of columns. For a matrix $`M`$, the last column is $`C = (c_1, \dots, c_N)`$, and $`M^-`$ is $`M`$ without $`C`$.
- $`t`$ is the lowest nonzero row of $`C`$: $`c_t \gt  0`$ and $`y \gt  t \Rightarrow c_y = 0`$.
- The bad root $`R = (r_1, \dots, r_N)`$ is given by the bad root rule of the rule set ([rules-en.md](rules-en.md)). The bad part $`B`$ is the columns from $`R`$ to the one just before $`C`$.
- $`\delta_y = c_y - r_y \ (y \lt  t)`$ and $`\delta_y = 0 \ (y \ge t)`$. The ascension flags $`a_{xy} \in \lbrace 0, 1\rbrace`$ are given by the ascension rule of the rule set.
- $`B_k = B + k (A \otimes \Delta)`$: add $`k a_{xy} \delta_y`$ to column $`x`$, row $`y`$ of $`B`$.
- The expansion is $`M[n] = M^- B_1 B_2 \cdots B_n`$. When $`C`$ is all zero or there is no bad root, $`M[n] = M^-`$.

In Lean this is `expand R M n` ([Expand.lean](../lean/Common/Expand.lean)). An expansion keeps every column except the last one, so $`M[n]`$ always starts with $`M^-`$, and $`M[0] = M^-`$.

## Computation and non-termination

The computation of the classification page updates the pair of a matrix and a bracket as follows, and stops when the matrix becomes empty.

```math
(M_0, n_0) = (M, n), \qquad (M_{i+1}, n_{i+1}) = (M_i[f(n_i)], f(n_i))
```

$`\mathrm{Halts}_R(M, n)`$ means that $`M_i`$ is empty for some $`i`$ (Lean: `Halts`). For each example we prove $`\forall n \ge 1, \neg \mathrm{Halts}_R(M, n)`$.

The general lemma below holds whatever $`f`$ is, as long as every bracket is at least 1. So it does not matter whether the copies are made before or after the bracket is changed to $`f(n)`$ (note 7 in [rules-en.md](rules-en.md)).

## Standard form

Let $`\iota_N = (0,\dots,0)(1,\dots,1)`$ with $`N`$ rows. $`M`$ is standard when the following holds (Lean: `Std`).

```math
\exists N, \exists n_1, \dots, n_m,\quad \iota_N[n_1][n_2]\cdots[n_m] = \mathrm{pad}_N(M)
```

$`\mathrm{pad}_N(M)`$ appends zeros below every column of $`M`$ up to $`N`$ rows. BMS matrices are usually written without their bottom zero rows. For example, $`(0,0,0)(1,1,1)(2,1,1)(1,1,1)`$ is reached from the 4-row $`(0,0,0,0)(1,1,1,1)`$ as $`(0,0,0,0)(1,1,1,0)(2,1,1,0)(1,1,1,0)`$.

Appending zero rows does not change expansions. For a matrix $`M`$ whose columns all have the same length, Lean proves the following ([Pad.lean](../lean/Common/Pad.lean)).

```math
\mathrm{pad}_N(M)[n] = \mathrm{pad}_N(M[n]), \qquad \mathrm{Halts}_R(\mathrm{pad}_N(M), n) \iff \mathrm{Halts}_R(M, n)
```

The main theorem of each example also states non-termination of the matrix with the zero rows appended.

## General lemma: a looping family implies non-termination

$`Y \sqsubseteq X`$ means that $`Y`$ is a prefix of $`X`$. Suppose a set $`S`$ of matrices satisfies the following two conditions (Lean: `Loop R S 1`).

1. $`\forall X \in S,\ X \ne ()`$
2. $`\forall X \in S,\ \forall n \ge 1,\ \exists Y \in S,\ Y \sqsubseteq X[n]`$

Then the following hold ([Loop.lean](../lean/Common/Loop.lean)).

- (a) `Loop.not_halts`: if $`f(n) \ge 1`$ for every $`n \ge 1`$, then $`\forall X \in S, \forall n \ge 1, \neg \mathrm{Halts}_R(X, n)`$.
- (b) `Loop.not_acc`, `Loop.infinite_descent`: no element of $`S`$ is well-founded for the expansion relation. There is an infinite sequence $`X = X_0, X_1, X_2, \dots`$ in which each $`X_{i+1}`$ equals some expansion of $`X_i`$.

**Proof outline.** The key fact is that for $`Z \ne ()`$ there is $`Z'`$ with $`(Y Z)[n] = Y Z'`$, because an expansion keeps every column except the last one. Start the computation from $`X \in S`$. The first step gives $`X[n] = Y Z`$ with $`Y \in S`$. After that, the computation either

- reaches exactly $`Y`$, or
- keeps $`Y`$ as a proper prefix forever.

In the second case it never becomes empty; in the first case the same argument repeats from $`Y \in S`$. Packing this into a strong induction on the number of steps before halting gives (a). (b) follows because a matrix with a prefix in $`S`$ always has a next step: from $`Y Z`$ we return to $`Y`$ by repeating $`[0]`$.

Each example consists of a concrete family $`S`$ with a proof of condition 2 (`Loop.lean`) and a standardness path (`Standard.lean`).

## Checks

- **Traces of the sources** (`lean/*/Trace.lean`): each line of the expansions written in the source is checked by `decide` against the definitions. Typos in the sources are recorded there.
- **Comparison with yaBMS** ([Test/YaBMS.lean](../lean/Test/YaBMS.lean)): the 72 matrices on the standardness paths and the loops of BM1.1 and BM2 are expanded with brackets 1 and 2. All 144 results agree with the output of `-v 1.1` / `-v 2` of [yaBMS](https://github.com/koteitan/yaBMS), checked by `decide`. The test is generated by [tools/crosscheck.sh](../tools/crosscheck.sh).
- **Axioms** ([Test/Axioms.lean](../lean/Test/Axioms.lean)): the main theorems use only `propext`, `Classical.choice` and `Quot.sound`. Neither `sorry` nor `native_decide` is used.

## Sources

| content | URL |
|---|---|
| the classification page (revision of 2023-02-10) | [User blog:Koteitan/バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E) |
| the examples of BM1 and BM1.1 (hyp cos) | [Talk:Bashicu matrix system](https://googology.fandom.com/wiki/Talk:Bashicu_matrix_system) ("Something wrong happens", "Still with problems") |
| the example of BM1 (Bubby3) | [User blog:Bubby3/BM1 is weaker than expected.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM1_is_weaker_than_expected.) |
| the example of BM2 (Bubby3) | [User blog:Bubby3/BM2 doesn't terminate.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM2_doesn%27t_terminate.) |
| the example of BM3 (Alemagno12) | [User blog:Alemagno12/BM3 has an infinite loop](https://googology.fandom.com/wiki/User_blog:Alemagno12/BM3_has_an_infinite_loop) |
| $`f`$ of BM3 (`A=A*A` in the BASIC code) | [BashicuHyudora/BASIC言語による巨大数のまとめ (oldid=14878)](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=14878) |
| the implementation used for the comparison | [yaBMS](https://github.com/koteitan/yaBMS) |
