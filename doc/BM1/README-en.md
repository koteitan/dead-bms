[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# BM1

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| left-adjacent method | all branches | none | $`n^2`$ |

- Left-adjacent method: let $`t`$ be the lowest nonzero row of the last column $`C`$. The bad root is the rightmost column left of $`C`$ with $`m_y \lt  c_y`$ for every row $`y \le t`$.
- All branches: every element of the bad part ascends.
- The definition is [BM1 (BASIC)](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=9843).

## Non-terminating examples

| number | matrix | source | explanation | Lean |
|---|---|---|---|---|
| 1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` | hyp cos | [1/README-en.md](1/README-en.md) | [lean/BM1/1](../../lean/BM1/1) |
| 2 | `(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)` | Bubby3 | [2/README-en.md](2/README-en.md) | [lean/BM1/2](../../lean/BM1/2) |

Neither source proves that its example is standard. The Lean proofs give explicit paths from ι.
