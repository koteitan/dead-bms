[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of BM2.1

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| Upper-Branch-Ignoring Model | all branches | none | $`n+1`$ |

The classification page says "停止しない" (does not terminate) and "BM1.1と同じ" (the same as BM1.1). The expansion rules of BM2.1 are those of BM1.1; only $`f(n) = n + 1`$ differs. So the [example of BM1.1](../BM1.1/README-en.md) is used.

The example of KurohaKafka listed on the page is on Twitter and could not be checked, so it is not covered.

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,1)`.

**Theorem** (`DeadBms.BM2_1.Ex.main` in [Main.lean](../../lean/BM2.1/Main.lean))

1. $`M`$ is standard in BM2.1.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ (with $`f(n) = n+1`$) does not halt. The same holds for $`\mathrm{pad}_4(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

## Proof

- The expansion is the same as that of BM1.1 (`expand_eq`, by `rfl`). So the standardness path and the conditions on the looping family $`S`$ carry over (`Std.of_expand_eq`, `Loop.of_expand_eq`).
- The remaining condition of the general lemma is "$`n \ge 1 \Rightarrow f(n) \ge 1`$", which holds for $`f(n) = n + 1`$.
