[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example 1 of BM1 (hyp cos)

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)`.

**Theorem** (`DeadBms.BM1.Ex1.main` in [Main.lean](../../../lean/BM1/1/Main.lean))

1. $`M`$ is standard in BM1.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_4(M)`$, with a zero row appended.
3. There is an infinite sequence $`M = X_0, X_1, X_2, \dots`$ in which each $`X_{i+1}`$ equals some expansion of $`X_i`$.

The terms and the general lemma are explained in [doc/README-en.md](../../README-en.md).

## Source

hyp cos, [Talk:Bashicu matrix system](https://googology.fandom.com/wiki/Talk:Bashicu_matrix_system), "Something wrong happens" (2016-04-28):

> (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)[n] reduces to (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)...[n], where (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)[n1] reduces to …

Each of these lines is reproduced in [Trace.lean](../../../lean/BM1/1/Trace.lean).

## Standardness

Expanding $`(0,0,0,0)(1,1,1,1)`$ with the following brackets gives $`\mathrm{pad}_4(M)`$ ([Standard.lean](../../../lean/BM1/1/Standard.lean), checked by `decide`). The bottom zero row is omitted below.

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
[1] (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,2,1)(3,1,0)
[0] (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,2,1)
[1] (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,2,0)
[2] (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)
```

## The loop

For $`k \ge 0`$ consider the following family. $`X_0 = M`$.

```math
X_k = P\ ((3,0,0)(2,1,0))^k\ (3,1,0), \qquad P = (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)
```

The expansion of $`X_k`$ goes as follows.

1. The last column is $`C = (3,1,0)`$, and $`t = 2`$.
2. The bad root of the left-adjacent method is the rightmost column with $`m_1 \lt  3`$ and $`m_2 \lt  1`$.
   - In the repeated part, $`(3,0,0)`$ has $`m_1 = 3`$ and $`(2,1,0)`$ has $`m_2 = 1`$, so neither qualifies.
   - In $`P`$, $`(2,1,0)`$ and $`(1,1,0)`$ have $`m_2 = 1`$ and do not qualify; the third column $`(2,0,0)`$ does.
   - So the bad root is $`R = (2,0,0)`$ for every $`k`$.
3. The bad part is $`B = (2,0,0)(1,1,0)(2,1,0)\ ((3,0,0)(2,1,0))^k`$, and $`\Delta = (3-2, 0, 0) = (1,0,0)`$.
4. All branches ascend, so $`B_1 = B + (1,0,0) = (3,0,0)(2,1,0)(3,1,0)\ ((4,0,0)(3,1,0))^k`$.
5. So for $`n \ge 1`$ the following holds.

```math
X_k[n] = X_k^-\ B_1 \cdots = P\ ((3,0,0)(2,1,0))^k\ (3,0,0)(2,1,0)(3,1,0) \cdots = X_{k+1} \cdots
```

$`X_{k+1}`$ is a prefix of $`X_k[n]`$. $`S = \lbrace X_k \mid k \ge 0 \rbrace`$ satisfies the conditions of the general lemma, so the computation starting from $`M = X_0`$ does not halt.

## Lean

| file | content |
|---|---|
| [Standard.lean](../../../lean/BM1/1/Standard.lean) | the standardness path |
| [Loop.lean](../../../lean/BM1/1/Loop.lean) | the family $`X_k`$; the bad root is always $`(2,0,0)`$ (`badRoot`), and the conditions of the general lemma (`loop`) |
| [Trace.lean](../../../lean/BM1/1/Trace.lean) | the trace of the source |
| [Main.lean](../../../lean/BM1/1/Main.lean) | the main theorem |
