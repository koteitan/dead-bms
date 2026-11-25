[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example 2 of BM1 (Bubby3)

## Statement

Let $`M =`$ `(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)`.

**Theorem** (`DeadBms.BM1.Ex2.main` in [Main.lean](../../../lean/BM1/2/Main.lean))

1. $`M`$ is standard in BM1.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_3(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

The terms and the general lemma are explained in [doc/README-en.md](../../README-en.md).

## Source

Bubby3, [User blog:Bubby3/BM1 is weaker than expected.](https://googology.fandom.com/wiki/User_blog:Bubby3/BM1_is_weaker_than_expected.) (2018-03):

> (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1) decomposes into (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)(5,1)(6,0)(5,1)(6,1)..., which eventually becomes (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1), which just keeps escalating forever when it encontours a (4,1).

This expansion is reproduced in [Trace.lean](../../../lean/BM1/2/Trace.lean).

The 2-row version of BM1 chooses different bad roots from the pair sequence system (PSS). For this $`M`$, the bad root is $`(3,0)`$ in BM1 and $`(0,0)`$ in BM4.

## Standardness

Expanding $`(0,0,0)(1,1,1)`$ with the following brackets gives $`\mathrm{pad}_3(M)`$ ([Standard.lean](../../../lean/BM1/2/Standard.lean)). The bottom zero row is omitted below.

```
    (0,0,0)(1,1,1)
[3] (0,0)(1,1)(2,2)(3,3)
[1] (0,0)(1,1)(2,2)(3,2)
[1] (0,0)(1,1)(2,2)(3,1)(4,2)
[0] (0,0)(1,1)(2,2)(3,1)
[1] (0,0)(1,1)(2,2)(3,0)(4,1)(5,2)
[0] (0,0)(1,1)(2,2)(3,0)(4,1)
[1] (0,0)(1,1)(2,2)(3,0)(4,0)
[1] (0,0)(1,1)(2,2)(3,0)(3,0)
[1] (0,0)(1,1)(2,2)(3,0)(2,2)(3,0)
[0] (0,0)(1,1)(2,2)(3,0)(2,2)
[1] (0,0)(1,1)(2,2)(3,0)(2,1)(3,2)(4,0)
[0] (0,0)(1,1)(2,2)(3,0)(2,1)(3,2)
[2] (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)
```

## The loop

For $`k \ge 0`$ consider the following family. $`X_0 = M`$.

```math
X_k = P\ ((4,0)(3,1))^k\ (4,1), \qquad P = (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)
```

The expansion of $`X_k`$ goes as follows.

1. The last column is $`C = (4,1)`$, and $`t = 2`$.
2. The bad root of the left-adjacent method is the rightmost column with $`m_1 \lt  4`$ and $`m_2 \lt  1`$.
   - In the repeated part, $`(4,0)`$ has $`m_1 = 4`$ and $`(3,1)`$ has $`m_2 = 1`$, so neither qualifies.
   - In $`P`$, $`(3,1)`$ and $`(2,1)`$ do not qualify; the fourth column $`(3,0)`$ does.
   - So the bad root is $`R = (3,0)`$ for every $`k`$.
3. The bad part is $`B = (3,0)(2,1)(3,1)\ ((4,0)(3,1))^k`$, and $`\Delta = (1,0)`$.
4. All branches ascend, so $`B_1 = (4,0)(3,1)(4,1)\ ((5,0)(4,1))^k`$.
5. So for $`n \ge 1`$ the following holds.

```math
X_k[n] = P\ ((4,0)(3,1))^k\ (4,0)(3,1)(4,1) \cdots = X_{k+1} \cdots
```

$`X_{k+1}`$ is a prefix of $`X_k[n]`$, so by the general lemma the computation starting from $`M = X_0`$ does not halt.

The matrix of Bubby3's "eventually becomes (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)" has $`X_1 = P\,(4,0)(3,1)\,(4,1)`$ as a prefix.

## Lean

| file | content |
|---|---|
| [Standard.lean](../../../lean/BM1/2/Standard.lean) | the standardness path |
| [Loop.lean](../../../lean/BM1/2/Loop.lean) | the family $`X_k`$; the bad root is always $`(3,0)`$ (`badRoot`), and the conditions of the general lemma (`loop`) |
| [Trace.lean](../../../lean/BM1/2/Trace.lean) | the trace of the source |
| [Main.lean](../../../lean/BM1/2/Main.lean) | the main theorem |
