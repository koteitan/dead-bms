[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of rTSS

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| left-adjacent method | all branches | none | $`n^2`$ |

rTSS uses the rules of BM1 on 3-row matrices (trio sequences). The classification page says "停止しない" (does not terminate) and "BM1のトリオ数列システムと同じ" (the same as the trio sequence system of BM1). So the 3-row example of BM1 ([example 1 of BM1](../BM1/1/README-en.md)) is used as it is.

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)`.

**Theorem** (`DeadBms.rTSS.Ex.main` in [Main.lean](../../lean/rTSS/Main.lean))

1. $`M`$ is reached from $`(0,0,0)(1,1,1)(2,2,2)`$ by 3-row expansions, with the brackets `1 1 0 1 1 0 1 1 1 1 1 0 1 0 1 2`.
2. $`M`$ is standard (in the sense of [doc/README-en.md](../README-en.md)).
3. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt.
4. $`M`$ has an infinite descending sequence.

## Proof

In the Lean definitions, `rTSS` and `BM1` are the same structure (`rTSS_eq : rTSS = BM1`, by `rfl`). So 2–4 are exactly the main theorem of example 1 of BM1.

1 is the path of example 1 of BM1 without its first bracket $`[2]`$. Since $`(0,0,0,0)(1,1,1,1)[2] = (0,0,0)(1,1,1)(2,2,2)`$ (with the bottom zero row omitted), the rest of the path only passes through 3-row matrices.
