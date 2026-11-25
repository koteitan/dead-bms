[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-terminating example of BM3 (Alemagno12)

| bad root search | bad part ascension | ascension modification | $`f(n)`$ |
|---|---|---|---|
| Upper-Branch-Ignoring Model | BM3 ascension | none | $`n^2`$ |

## Statement

Let $`M =`$ `(0,0,0)(1,1,1)(2,1,1)(1,1,1)`.

**Theorem** (`DeadBms.BM3.Ex.main` in [Main.lean](../../lean/BM3/Main.lean))

1. $`M`$ is standard in BM3.
2. For every $`n \ge 1`$, the computation starting from $`M[n]`$ does not halt. The same holds for $`\mathrm{pad}_4(M)`$, with a zero row appended.
3. $`M`$ has an infinite descending sequence.

The terms and the general lemma are explained in [doc/README-en.md](../README-en.md).

## Source

Alemagno12, [User blog:Alemagno12/BM3 has an infinite loop](https://googology.fandom.com/wiki/User_blog:Alemagno12/BM3_has_an_infinite_loop) (2018-06-29).

The source first shows that $`M`$ is standard, starting from $`(0,0,0,0)(1,1,1,1)`$, and then that the following sequence continues forever.

```
(0,0,0)(1,1,1)(2,1,1)(1,1,0)(2,2,1)(3,1,1)
(0,0,0)(1,1,1)(2,1,1)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,1)
…
```

Each line of the second part is reproduced in [Trace.lean](../../lean/BM3/Trace.lean).

The third line of the source reads `…(7,3,1)(8,1,1)(9,3,0)…`, but the expansion given by the definitions is `…(7,3,1)(8,1,1)(7,3,0)(8,4,1)(9,3,0)…`: two columns are missing. The proof only uses a prefix that ends before this place, so the conclusion is not affected.

## Standardness

Expanding $`(0,0,0,0)(1,1,1,1)`$ with the following brackets gives $`\mathrm{pad}_4(M)`$ ([Standard.lean](../../lean/BM3/Standard.lean)). The bottom zero row is omitted below.

```
    (0,0,0,0)(1,1,1,1)
[2] (0,0,0)(1,1,1)(2,2,2)
[1] (0,0,0)(1,1,1)(2,2,1)
[1] (0,0,0)(1,1,1)(2,2,0)(3,3,1)
[0] (0,0,0)(1,1,1)(2,2,0)
[2] (0,0,0)(1,1,1)(2,1,1)(3,1,1)
[1] (0,0,0)(1,1,1)(2,1,1)(3,1,0)(4,2,1)(5,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(3,1,0)(4,2,1)
[0] (0,0,0)(1,1,1)(2,1,1)(3,1,0)
[1] (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(3,0,0)
[1] (0,0,0)(1,1,1)(2,1,1)(2,1,1)
[1] (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,1)(4,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,1)
[0] (0,0,0)(1,1,1)(2,1,1)(2,1,0)
[1] (0,0,0)(1,1,1)(2,1,1)(2,0,0)(3,1,1)(4,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(2,0,0)(3,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(2,0,0)
[1] (0,0,0)(1,1,1)(2,1,1)(1,1,1)(2,1,1)
[0] (0,0,0)(1,1,1)(2,1,1)(1,1,1)
```

## The loop

For $`k \ge 0`$ consider the following family. $`X_0 = M`$.

```math
X_k = (0,0,0)(1,1,1)(2,1,1)\ \prod_{j=0}^{k-1} (2j+1,1,0)(2j+2,2,1)\ (2k+1,1,1)
```

### The bad root is column 1

The last column is $`C = (2k+1, 1, 1)`$, and $`t = 3`$. $`X_k`$ has the following properties.

- Column 1 is $`(0,0,0)`$.
- Every other column is positive in row 1.
- Every column other than column 1 and the last one is at least $`1 = c_2`$ in row 2.
- $`c_2, c_3 \gt  0`$.

Under these conditions the bad root of the Upper-Branch-Ignoring Model is column 1 (the general theorem `ubim_eq_zero` in [Ubim.lean](../../lean/Common/Ubim.lean)).

1. Following the row-1 ancestors always reaches column 1.
2. Every column on the way is at least $`c_2`$ in row 2, so the row-2 parent is column 1.
3. The row-3 parent is also column 1.

### The expansion

$`B = X_k^-`$ and $`\Delta = (2k+1, 1, 0)`$. The BM3 flags of the first 3 columns $`(0,0,0)(1,1,1)(2,1,1)`$ of $`B`$ are:

- $`(0,0,0)`$: all 1
- $`(1,1,1)`$: all 1
- $`(2,1,1)`$: 1 in row 1, 0 in row 2 (row 2 of $`p = (1,1,1)`$ is $`1`$, which is not smaller than $`1`$)

The first 3 columns of $`B_1`$ are $`(2k+1,1,0)(2k+2,2,1)(2k+3,1,1)`$. So for $`n \ge 1`$ the following holds.

```math
X_k[n] = X_k^-\ (2k+1,1,0)(2k+2,2,1)(2k+3,1,1) \cdots = X_{k+1} \cdots
```

$`X_{k+1}`$ is a prefix of $`X_k[n]`$, so by the general lemma the computation starting from $`M = X_0`$ does not halt.

## Lean

| file | content |
|---|---|
| [Standard.lean](../../lean/BM3/Standard.lean) | the standardness path |
| [Loop.lean](../../lean/BM3/Loop.lean) | the family $`X_k`$; the bad root is column 1 (`badRoot`), the beginning of $`B_1`$ (`first_copy`), and the conditions of the general lemma (`loop`) |
| [Trace.lean](../../lean/BM3/Trace.lean) | the trace of the source |
| [Main.lean](../../lean/BM3/Main.lean) | the main theorem |
