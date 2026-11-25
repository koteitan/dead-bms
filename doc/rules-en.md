[← Back](../README.md) | [English](rules-en.md) | [Japanese](rules.md)

# The rules of the classification page and their Lean definitions

The seven rule sets marked as non-terminating on the classification page are covered. All of them use no ascension modification (改変なし), so the ascension flags are $`a_{xy} = a'_{xy}`$.

| rule set | bad root search | bad part ascension | $`f(n)`$ | Lean |
|---|---|---|---|---|
| BM1 | left-adjacent method (左隣法) | all branches (全枝有効方式) | $`n^2`$ | `BM1` |
| rTSS | left-adjacent method | all branches | $`n^2`$ | `rTSS` |
| BM1.1 | Upper-Branch-Ignoring Model (上行枝無視方式) | all branches | $`n^2`$ | `BM1_1` |
| BM2.1 | Upper-Branch-Ignoring Model | all branches | $`n+1`$ | `BM2_1` |
| Bubby3's fix | Upper-Branch-Ignoring Model | all branches | $`n^2`$ | `Bubby3fix` |
| BM2 | Upper-Branch-Ignoring Model | BM2 ascension (BM2 方式) | $`n^2`$ | `BM2` |
| BM3 | Upper-Branch-Ignoring Model | BM3 ascension (BM3 方式) | $`n^2`$ | `BM3` |

The definitions are in [Rules.lean](../lean/Common/Rules.lean), [BadRoot.lean](../lean/Common/BadRoot.lean), [Ascend.lean](../lean/Common/Ascend.lean) and [Expand.lean](../lean/Common/Expand.lean).

The following rule sets are not covered, because the page does not say that they do not terminate.

- The page only says "considered broken" or "expected not to terminate": BM3.1, BM3.2, BM3.1.1.
- The page says nothing about non-termination: BM4, BM2.3, BM2.2.

## Bad root search

- **Left-adjacent method** (`leftAdj`): the rightmost column $`M`$ left of $`C`$ with $`m_y \lt  c_y`$ for row $`t`$ and every row above it ($`y \le t`$).
- **Upper-Branch-Ignoring Model** (`parent`, `ubim`): the parent of an element $`c`$ is the rightmost element $`m`$ that satisfies all of the following.
  - It is in the same row as $`c`$.
  - It is left of $`c`$.
  - It is smaller than $`c`$.
  - It is in the top row, or in the same column as one of the ancestors of the element just above $`c`$.

  The ancestors of $`c`$ are $`c`$ itself and the parents of its ancestors. The bad root is the column of the parent of $`c_t`$.

## Bad part ascension

Column $`x = 1`$ of $`B = (b_{xy})`$ is the bad root. Let $`p(x) = \max\lbrace k \mid k \lt  x \land b_{k1} \lt  b_{x1}\rbrace`$.

- **All branches** (`ascAll`): $`a'_{xy} = 1`$.
- **BM2 ascension** (`ascBM2`): $`a'_{1y} = 1`$. For $`x \gt  1`$, $`a'_{xy} = 1 \iff a'_{p(x)y} = 1 \land r_y \lt  b_{xy}`$.
- **BM3 ascension** (`ascBM3`): $`a'_{x1} = 1`$ and $`a'_{1y} = 1`$. For $`x \gt  1`$, $`a'_{xy} = 1 \iff a'_{p(x)y} = 1 \land b_{p(x)y} \lt  b_{xy}`$.

When $`p(x)`$ does not exist, $`a'_{xy} = 0`$.

## How the page is read

In three places the page does not make sense when read literally. They are read as follows, and each reading is confirmed by the traces of the sources or by the comparison with yaBMS.

1. **The inequality of the left-adjacent method**: the page writes "$`m_y \gt  c_y`$", read as $`m_y \lt  c_y`$. This agrees with the BM1 traces of hyp cos and Bubby3 ([BM1/1/Trace.lean](../lean/BM1/1/Trace.lean), [BM1/2/Trace.lean](../lean/BM1/2/Trace.lean)).
2. **$`b_{r_y y}`$ in the BM2 ascension**: the page writes "$`b_{r_y y} \lt  b_{xy}`$", read as $`r_y \lt  b_{xy}`$, where $`r_y`$ is row $`y`$ of the bad root. This agrees with the BM2 trace of Bubby3 ([BM2/Trace.lean](../lean/BM2/Trace.lean)) and with 144 outputs of yaBMS `-v 2`.
3. **The direction in the BM3 ascension**: the text says "$`b_{xy}`$ is smaller than $`b_{p(x)y}`$", but the formula says $`b_{p(x)y} \lt  b_{xy}`$. The formula is used. This agrees with the trace of Alemagno12 ([BM3/Trace.lean](../lean/BM3/Trace.lean)).

## Other notes

4. **$`f`$ of BM3**: the page does not give it. The BASIC code of BM3 has `A=A*A`, so $`f(n) = n^2`$.
5. **rTSS**: treated as the rules of BM1 restricted to 3-row matrices, following "BM1のトリオ数列システムと同じ" (the same as the trio sequence system of BM1) on the page.
6. **BM2.1 and Bubby3's fix**: the same expansion rules as BM1.1 ("BM1.1と同じ" on the page). BM2.1 differs only in $`f(n) = n + 1`$. The example of KurohaKafka for BM2.1 is on Twitter and could not be checked, so the example of BM1.1 is used.
7. **Updating the bracket**: the procedure of the page changes [n] to [f(n)] and then copies "according to the value of the bracket $`n`$", so it is not clear which value is used. `compute` in Lean copies $`f(n)`$ times, using the new value. The general lemma holds whenever every bracket is at least 1, so the conclusion is the same for either reading.
8. **Zero rows**: the standardness paths start from $`\iota_{N+1}`$, which has one more row. It is proved that appending zero rows changes neither the expansions nor halting (section "Standard form" of [README-en.md](README-en.md)).
