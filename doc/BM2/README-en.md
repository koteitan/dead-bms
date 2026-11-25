[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of BM2 (Bubby3)

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| Upper-Branch-Ignoring Model | BM2 ascension | none | $`n^2`$ |

## Statement

Let $`M =`$ `(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)`.

**Theorem** (`DeadBms.BM2.Ex.main` in [Main.lean](../../lean/BM2/Main.lean))

1. $`M`$ is standard in BM2.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_5(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

The terms and the general lemma are explained in [doc/README-en.md](../README-en.md).

## Source

Bubby3, [User blog:Bubby3/BM2 doesn't terminate.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM2_doesn%27t_terminate.) (2018-08).

The source proves standardness by a chain of ">" from $`(0,0,0,0,0)(1,1,1,1,1)`$, and non-termination by a sequence of expansions starting at $`(7,3,1,1)`$. Each line of the latter is reproduced in [Trace.lean](../../lean/BM2/Trace.lean).

## Standardness

$`\mathrm{pad}_5(M)`$ is reached from $`(0,0,0,0,0)(1,1,1,1,1)`$ by 36 expansions ([Standard.lean](../../lean/BM2/Standard.lean)). The brackets are:

```
2 1 1 0 3 1 0 0 0 1 0 0 0 1 1 0 0 0 1 0 0 0 1 0 1 0 0 0 1 0 0 1 1 1 1 0
```

All 16 matrices of the ">" chain of the source appear on this path.

## The loop

For $`k \ge 0`$ consider the following family. $`X_0 = M`$.

```math
X_k = P\ D_0 D_1 \cdots D_{k-1}\ (7+6k,\ 3+2k,\ 1,\ 1)
```

where:

- $`P = (0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)`$
- $`D_0 = (7,3,1,0)(8,4,2,1)(9,5,2,1)(10,6,2,1)(11,5,0,0)(12,4,1,1)`$
- $`D_j = D_0 + (6j, 2j, 0, 0)`$

### The bad root is column 1

The last column is $`C = (7+6k, 3+2k, 1, 1)`$, and $`t = 4`$.

1. **Row 1 strictly increases** ($`0, 1, 2, \dots, 7+6k`$). So the row-1 ancestors of each column are all the columns left of it, and the row-2 parent is the rightmost column on the left with a smaller row-2 entry.
2. Apart from column 1, the columns whose row 3 is 0 are $`(4,2,0,0)`$ and $`(11+6j, 5+2j, 0, 0)`$. The column just right of each is smaller in row 2 ($`(5,1,1,1)`$ and $`(12+6j, 4+2j, 1, 1)`$). So none of them is the row-2 parent of any column.
3. Hence every row-2 ancestor of $`C`$ other than column 1 has row 3 at least $`1 = c_3`$. Column 1 is an ancestor: its row 2 is 0, so following the ancestors always reaches it. So **the row-3 parent is column 1**.
4. The row-4 parent is also column 1 ($`0 \lt  1`$).

### The expansion

The bad root is column 1, so $`B = X_k^-`$ and $`\Delta = (7+6k, 3+2k, 1, 0)`$.

The BM2 flag of each column $`x`$ is determined by following $`p(x)`$, so the flags of the first 7 columns of $`B`$ ($`= P`$) depend only on $`P`$. They are (row 4 does not matter since $`\delta_4 = 0`$):

| column of $`P`$ | row 1 | row 2 | row 3 |
|---|---|---|---|
| (0,0,0,0) | 1 | 1 | 1 |
| (1,1,1,1) | 1 | 1 | 1 |
| (2,2,1,1) | 1 | 1 | 1 |
| (3,3,1,1) | 1 | 1 | 1 |
| (4,2,0,0) | 1 | 1 | 0 |
| (5,1,1,1) | 1 | 1 | 0 |
| (6,2,1,1) | 1 | 1 | 0 |

The first 7 columns of $`B_1`$ are $`P + A \otimes \Delta = D_k\ (7+6(k+1), 3+2(k+1), 1, 1)`$. So for $`n \ge 1`$ the following holds.

```math
X_k[n] = X_k^-\ D_k\ (13+6k, 5+2k, 1, 1) \cdots = X_{k+1} \cdots
```

$`X_{k+1}`$ is a prefix of $`X_k[n]`$, so by the general lemma the computation starting from $`M = X_0`$ does not halt.

## Lean

| file | content |
|---|---|
| [Standard.lean](../../lean/BM2/Standard.lean) | the standardness path |
| [Loop.lean](../../lean/BM2/Loop.lean) | the family $`X_k`$; the property of adjacent columns (`adj_X`), the bad root is column 1 (`badRoot`), the beginning of $`B_1`$ (`first_copy`), and the conditions of the general lemma (`loop`) |
| [Trace.lean](../../lean/BM2/Trace.lean) | the trace of the source |
| [Main.lean](../../lean/BM2/Main.lean) | the main theorem |
