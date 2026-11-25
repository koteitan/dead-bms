[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of BM1.1 (hyp cos)

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| Upper-Branch-Ignoring Model | all branches | none | $`n^2`$ |

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,1)`.

**Theorem** (`DeadBms.BM1_1.Ex.main` in [Main.lean](../../lean/BM1.1/Main.lean))

1. $`M`$ is standard in BM1.1.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_4(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

The terms and the general lemma are explained in [doc/README-en.md](../README-en.md).

## Source

hyp cos, [Talk:Bashicu matrix system](https://googology.fandom.com/wiki/Talk:Bashicu_matrix_system), "Still with problems" (2016-05-23):

> Continue upward, we get (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,2,1)(3,0,0)...(k,k,0)(k+1,k+1,1)(k+2,0,0)(k+1,k+1,1), and we can never solve (0,0,0)(1,1,1)(2,0,0)(1,1,1)[n].

For each of the 12 lines of the two periods in the source, [Trace.lean](../../lean/BM1.1/Trace.lean) checks two things.

- The right-hand side is a prefix of the expansion.
- The bad root is the first column of the bad part stated in the source.

## Standardness

Expanding $`(0,0,0,0)(1,1,1,1)`$ with the following brackets gives $`\mathrm{pad}_4(M)`$ ([Standard.lean](../../lean/BM1.1/Standard.lean)). The bottom zero row is omitted below.

```
    (0,0,0,0)(1,1,1,1)
[2] (0,0,0)(1,1,1)(2,2,2)
[1] (0,0,0)(1,1,1)(2,2,1)
[1] (0,0,0)(1,1,1)(2,2,0)(3,3,1)
[0] (0,0,0)(1,1,1)(2,2,0)
[1] (0,0,0)(1,1,1)(2,1,1)
[1] (0,0,0)(1,1,1)(2,1,0)(3,2,1)
[0] (0,0,0)(1,1,1)(2,1,0)
[1] (0,0,0)(1,1,1)(2,0,0)(3,1,1)
[1] (0,0,0)(1,1,1)(2,0,0)(3,1,0)
[1] (0,0,0)(1,1,1)(2,0,0)(3,0,0)
[1] (0,0,0)(1,1,1)(2,0,0)(2,0,0)
[1] (0,0,0)(1,1,1)(2,0,0)(1,1,1)(2,0,0)
[0] (0,0,0)(1,1,1)(2,0,0)(1,1,1)
```

## The loop

Let:

- $`T_j = (j,j,0)(j+1,j+1,1)(j+2,0,0)`$
- $`Q_k = T_0 T_1 \cdots T_k`$
- $`E_k = (k+1,k+1,0)(k+2,k+2,1)`$

Then $`Q_{k+1} = Q_k E_k (k+3,0,0)`$. One period consists of the following six matrices, and $`s_0(0) = M`$.

| phase | matrix | $`t`$ | bad root | next matrix |
|---|---|---|---|---|
| $`s_0(k)`$ | $`Q_k\ (k+1,k+1,1)`$ | 3 | the first column $`(k,k,0)`$ of $`T_k`$ | $`s_1(k)`$ |
| $`s_1(k)`$ | $`Q_k E_k\ (k+3,1,0)`$ | 2 | column 1, $`(0,0,0)`$ | $`s_2(k)`$ |
| $`s_2(k)`$ | $`Q_k E_k (k+3,0,0)\ (k+4,1,1)`$ | 3 | $`(k+3,0,0)`$ | $`s_3(k)`$ |
| $`s_3(k)`$ | $`Q_k E_k (k+3,0,0)\ (k+4,1,0)`$ | 2 | $`(k+3,0,0)`$ | $`s_4(k)`$ |
| $`s_4(k)`$ | $`Q_k E_k (k+3,0,0)\ (k+4,0,0)`$ | 1 | $`(k+3,0,0)`$ | $`s_5(k)`$ |
| $`s_5(k)`$ | $`Q_k E_k (k+3,0,0)\ (k+3,0,0)`$ | 1 | $`(k+2,k+2,1)`$ | $`s_0(k+1)`$ |

All branches ascend, so $`B_1 = B + \Delta`$. The value of $`\Delta`$ and the beginning of $`B_1`$ in each phase are below; in every phase the next matrix is a prefix of the expansion for $`n \ge 1`$.

- **$`s_0(k)`$**: the bad root is found as follows.
  - Row 1: the rightmost column on the left whose row 1 is smaller than $`k+1`$ is the first column $`(k,k,0)`$ of $`T_k`$.
  - Row 2: row 2 of $`(k,k,0)`$ is $`k \lt  k+1`$, so the row-2 parent is the same column.
  - Row 3: row 3 is $`0 \lt  1`$, so the row-3 parent is also the same column.

  $`B = T_k`$, $`\Delta = (1,1,0)`$, $`B_1 = (k+1,k+1,0)(k+2,k+2,1)(k+3,1,0)`$, and $`s_0(k)^- B_1 = s_1(k)`$.
- **$`s_1(k)`$**: the bad root is column 1 (see below). $`B = s_1(k)^-`$, $`\Delta = (k+3,0,0)`$, and $`B_1`$ starts with $`(k+3,0,0)(k+4,1,1)\cdots`$.
- **$`s_2(k)`$, $`s_3(k)`$, $`s_4(k)`$**: the column $`(k+3,0,0)`$ just left of the last column is smaller than it in every row, so it is the bad root. $`\Delta`$ is $`(1,1,0)`$, $`(1,0,0)`$, $`(0,0,0)`$ respectively, and $`B_1`$ is $`(k+4,1,0)`$, $`(k+4,0,0)`$, $`(k+3,0,0)`$ respectively.
- **$`s_5(k)`$**: $`(k+3,0,0)`$ has the same row 1, so it is not the bad root. The column $`(k+2,k+2,1)`$ left of it is. $`\Delta = 0`$, so $`B_1 = (k+2,k+2,1)(k+3,0,0)`$, and $`s_5(k)^-\,(k+2,k+2,1) = Q_{k+1}\,(k+2,k+2,1) = s_0(k+1)`$.

### The bad root of $`s_1(k)`$ is column 1

Follow the row-1 ancestors of the last column $`(k+3,1,0)`$. The row-1 parent of a column is the rightmost column on the left with a smaller row-1 entry.

A column of the form $`(j+2,0,0)`$ (row 2 is 0) is immediately followed by $`(j+1,j+1,0)`$, which is smaller in row 1. Therefore $`(j+2,0,0)`$ is not the row-1 parent of any column.

- For its right neighbour $`(j+1,j+1,0)`$ itself, $`(j+2,0,0)`$ is not smaller, so it is not the parent.
- For any column further right, $`(j+1,j+1,0)`$ is found first.

So every row-1 ancestor of the last column other than column 1 has row 2 at least $`1 = c_2`$. Column 1, $`(0,0,0)`$, is an ancestor: its row 1 is 0, so following the ancestors always reaches it. Hence the row-2 parent is column 1.

In Lean, the argument "a column followed by a smaller column is never a parent" is `findLastIdx_take_ne`, and the property of adjacent columns is handled by `Adj`.

## Lean

| file | content |
|---|---|
| [Standard.lean](../../lean/BM1.1/Standard.lean) | the standardness path |
| [Loop.lean](../../lean/BM1.1/Loop.lean) | the six-phase family; the bad roots (`root0`, `root1`), the expansions (`step0`–`step5`), and the conditions of the general lemma (`loop`) |
| [Trace.lean](../../lean/BM1.1/Trace.lean) | the trace of the source |
| [Main.lean](../../lean/BM1.1/Main.lean) | the main theorem |
