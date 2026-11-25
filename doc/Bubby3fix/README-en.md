[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of Bubby3's fix

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| Upper-Branch-Ignoring Model | all branches | none | $`n^2`$ |

The classification page says "停止しない" (does not terminate) and "BM1.1と同じ" (the same as BM1.1). The rules of Bubby3's fix are exactly those of BM1.1. So the [example of BM1.1](../BM1.1/README-en.md) is used.

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,1)`.

**Theorem** (`DeadBms.Bubby3fix.Ex.main` in [Main.lean](../../lean/Bubby3fix/Main.lean))

1. $`M`$ is standard in Bubby3's fix.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_4(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

## Proof

In the Lean definitions, `Bubby3fix` and `BM1_1` are the same structure (`Bubby3fix_eq : Bubby3fix = BM1_1`, by `rfl`). So this is exactly the main theorem of BM1.1.
