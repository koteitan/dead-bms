[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-termination of Bismuth (version of 2020-07-15)

## Bismuth

Bismuth is a Y-sequence-like notation by Syst3ms ([User blog:Syst3ms/Bismuth : not Y sequence, but close](https://googology.fandom.com/wiki/User_blog:Syst3ms/Bismuth_:_not_Y_sequence,_but_close)). The blog post does not describe the expansion rules; the definition is the Kotlin program [Syst3ms/Bismuth](https://github.com/Syst3ms/Bismuth) itself.

The version treated here is the latest commit of the repository, [`bf7ba654`](https://github.com/Syst3ms/Bismuth/blob/bf7ba654/src/io/github/syst3ms/bismuth/Bismuth.kt) (2020-07-14 21:25 UTC, 2020-07-15 in Japan, "Fix diagonal finding&expansion method"). The version of 2019-09-29 is treated in [1y-bismuth](../1y-bismuth/README-en.md).

The expansion of a sequence $`X`$ with bracket $`n`$ is written $`X[n]`$. The program also accepts $`(\ldots)[0]`$, so brackets are $`n \ge 0`$. Integers are unbounded integers (Bismuth is read as a mathematical notation).

## Result

Let $`X = (1,4,12,9,12,20)`$. The following is proved in Lean (`Bismuth2020.main_theorem` in [Main.lean](../../lean/1y-bismuth-2020-07-15/Main.lean)).

1. $`X`$ is standard: it is obtained from $`(1,5)`$ by 58 expansions, with the brackets 0 and 1.
2. For every $`n`$ with $`0 \le n \le 20`$, the computation of $`X[n]`$ by the program does not end.

The case $`n \gt 20`$ is not proved.

## Standardness

Expanding $`(1,5)`$ with the following brackets gives $`X`$ ([Standard.lean](../../lean/1y-bismuth-2020-07-15/Standard.lean), checked by computation in Lean).

```
    (1,5)
[1] (1,4,16)
[0] (1,4,15)
[0] (1,4,14)
[0] (1,4,13)
[1] (1,4,12,32)
[0] (1,4,12,31)
[0] (1,4,12,30)
[0] (1,4,12,29)
[0] (1,4,12,28)
[0] (1,4,12,27)
[0] (1,4,12,26)
[1] (1,4,12,25)
[0] (1,4,12,24)
[0] (1,4,12,23)
[0] (1,4,12,22)
[0] (1,4,12,21)
[1] (1,4,12,20)
[0] (1,4,12,19)
[0] (1,4,12,18)
[0] (1,4,12,17)
[0] (1,4,12,16)
[1] (1,4,12,15,23)
[0] (1,4,12,15,22)
[0] (1,4,12,15,21)
[0] (1,4,12,15,20)
[0] (1,4,12,15,19)
[0] (1,4,12,15)
[0] (1,4,12,14)
[0] (1,4,12,13)
[1] (1,4,12,12)
[0] (1,4,12,11)
[0] (1,4,12,10)
[1] (1,4,12,9,21,55,49)
[0] (1,4,12,9,21,55,48)
[0] (1,4,12,9,21,55,47)
[0] (1,4,12,9,21,55,46)
[0] (1,4,12,9,21,55)
[0] (1,4,12,9,21,54)
[0] (1,4,12,9,21,53)
[0] (1,4,12,9,21,52)
[0] (1,4,12,9,21,51)
[0] (1,4,12,9,21,50)
[0] (1,4,12,9,21,49)
[0] (1,4,12,9,21,48)
[0] (1,4,12,9,21,47)
[0] (1,4,12,9,21,46)
[0] (1,4,12,9,21)
[0] (1,4,12,9,20)
[0] (1,4,12,9,19)
[0] (1,4,12,9,18)
[0] (1,4,12,9,17)
[1] (1,4,12,9,16)
[0] (1,4,12,9,15)
[1] (1,4,12,9,14)
[0] (1,4,12,9,13)
[1] (1,4,12,9,12,20,17)
[0] (1,4,12,9,12,20,16)
[0] (1,4,12,9,12,20)
```

## The expansion rules

This section gives the part of the expansion rules, as read from the program, that this example uses. Positions and rows are counted from 0. The program computes $`X[n]`$ with the number of copies $`t = n + 1`$; the rules below are written with $`t`$.

### Mountain

From a sequence $`X = (X_0, \dots, X_{L-1})`$, rows $`V_0, V_1, \dots, V_R`$ (each of length $`L`$) and the distances to the parents $`O_0, \dots, O_R`$ of each row are computed. These two tables are called the mountain and the distance table.

- $`V_0 = X`$.
- The parent $`P`$ of position $`i`$ in row $`r`$ is found by the following search.
  - The search starts at $`j = i - 1`$ if $`r = 0`$, and at $`j = i - \max(O_{r-1}(i), 0)`$ if $`r \ge 1`$.
  - While $`j \ge 0`$, repeat: if $`1 \le V_r(j) \lt V_r(i)`$, then $`P = j`$ and the search ends; if $`V_r(j) = 0`$, there is no parent; otherwise $`j`$ moves left by $`\max(O_r(j), 1)`$ (a distance not yet determined counts as 0).
- $`V_{r+1}(i) = V_r(i) - V_r(P)`$. If there is no parent, $`V_{r+1}(i) = 0`$.
- The distance is $`O_r(i) = i - P`$ if there is a parent. Otherwise $`O_r(i) = 0`$ when $`V_r(i) = 0`$ or $`V_r(0), \dots, V_r(i-1)`$ are all 0, and $`O_r(i) = -V_r(i)`$ else.
- Rows are added as long as the last position $`L - 1`$ has a parent in the top row (the details of this test are omitted).
- **The distances $`O_R`$ of the top row are not computed and stay 0.**

### Two cases

The expansion of $`X`$ depends on the bottom-right value $`V_R(L-1)`$ of the mountain.

- If $`V_R(L-1) \le 1`$ (ordinary expansion): the part from the bad root $`b = (L-1) - O_{R-1}(L-1)`$ to position $`L-2`$ is repeated $`t`$ times. On the way, the distance table is widened by the copy procedure (next subsection). How the values are set while repeating does not matter for why this example does not stop, so it is omitted here.
- If $`V_R(L-1) \ge 2`$: the expansion along a path (the subsection after next) is used.

### Copy procedure

This procedure widens a table $`M`$ with $`h`$ rows and $`w`$ columns (rows $`M_0, \dots, M_{h-1}`$), given a position $`b`$ and a number of copies $`t`$.

1. Let $`c = w - 1 - b`$, the number of columns to the right of $`b`$, and let the width be $`W = b + c\,t + 1`$.
2. Append zeros to every row to make $`W`$ columns.
3. While the last entry $`M_0(W-1)`$ of the first row is 0, repeat the following for $`k = 1, 2, 3, \dots`$ in order.
   - For $`j = 0, 1, \dots, c-1`$ in order, let the target be $`q = b + k c + j + 1`$. If $`q \ge W`$, this round ends here. Otherwise, in every row, copy the value $`v`$ of column $`b + j + 1`$ to column $`q`$; when $`v \gt j + 1`$, copy $`v + k c`$ instead.

### Expansion along a path

If $`V_R(L-1) \ge 2`$, the expansion is computed as follows.

1. For each position $`x`$, let $`y(x)`$ be the top row with $`V_y(x) \gt 0`$. The points $`(x, y(x))`$ from left to right are called the path, and the sequence of the values on the path is $`D = (V_{y(0)}(0), \dots, V_{y(L-1)}(L-1))`$.
2. For each position $`x`$, a distance $`F(x)`$ of row 0 of $`D`$ is determined from the mountain and the distance table. How it is computed does not directly matter for why this example does not stop, so only the values are given.
3. $`D`$ is expanded with the number of copies $`t + 1`$, using $`F`$ as the distances of row 0 of the mountain of $`D`$. Let $`b_D`$ be the bad root of $`D`$.
4. Take the point $`(b_D, y(b_D))`$ of the path at position $`b_D`$. Cut out row $`y(b_D)`$ of the distance table from position $`b_D`$ to the right end. This is called the bad part.
5. The bad part (a table with one row) is widened by the copy procedure, with position 0 and number of copies $`t`$.
6. Then the new table is assembled. This example never gets past step 5, so the rest is omitted.

## Why X[n] does not stop

### The mountain of X

```
position  0  1  2  3  4  5
V_0       1  4 12  9 12 20
V_1       0  3  8  5  3  8
V_2       0  0  5  2  0  5

O_0       0  1  1  2  1  1
O_1       0  0  1  2 -3  1
O_2       0  0  0  0  0  0
```

$`R = 2`$ and the bottom-right value is $`V_2(5) = 5 \ge 2`$, so the expansion along a path is used. The distances $`O_2`$ of the top row are not computed, so they are all 0.

### The path and D

```
position      0  1  2  3  4  5
y(x)          0  1  2  2  1  2
D             1  3  5  2  3  5
F             0  1  1  3  4  1
```

### The expansion of D

$`D = (1,3,5,2,3,5)`$ is expanded with the number of copies $`t + 1`$, using $`F`$ as the distances of row 0. The mountain of $`D`$ is as follows.

```
position  0  1  2  3  4  5
V_0       1  3  5  2  3  5
V_1       0  2  2  1  2  2
V_2       0  0  0  0  0  1

O_0       0  1  1  3  4  1
O_1       0  0 -2 -1 -2  2
O_2       0  0  0  0  0  0
```

The bottom-right value is $`V_2(5) = 1`$, so this is an ordinary expansion, with bad root $`b_D = 5 - O_1(5) = 3`$. This expansion ends.

### The bad part

The point of the path at position 3 is $`(3, y(3)) = (3, 2)`$. Cutting out positions 3 to 5 of row 2 of the distance table gives the bad part

```math
(O_2(3), O_2(4), O_2(5)) = (0, 0, 0)
```

Row 2 is the top row, so its distances were never computed and are still 0.

### The copy procedure does not end

The bad part $`(0,0,0)`$ is widened with position $`b = 0`$ and number of copies $`t = n+1`$. Since $`w = 3`$, $`c = 2`$ and the width is $`W = 2(n+1) + 1 = 2n + 3`$. Every copied value is 0, so copying leaves everything 0. For $`n = 2`$ ($`W = 7`$) the table (one row) is as follows.

```
start    0 0 0 0 0 0 0   last entry is 0, so continue
round 1  0 0 0 0 0 0 0   copy (0, 0) of columns 1, 2 to columns 3, 4; last entry is 0, so continue
round 2  0 0 0 0 0 0 0   copy (0, 0) of columns 1, 2 to columns 5, 6; last entry is 0, so continue
round 3  0 0 0 0 0 0 0   target 7 is not below the width 7, nothing is copied; last entry is 0, so continue
round 4  0 0 0 0 0 0 0   the same
…
```

The table never changes and the last entry stays 0, so the repetition never ends. Hence the computation of $`X[n]`$ does not end. Only the width $`W = 2n + 3`$ depends on $`n`$.

In the example of the version of 2019-09-29 ([1y-bismuth](../1y-bismuth/README-en.md)), there were no columns to copy. Here there are two columns to copy, but all the copied values are 0.

## How it is formalized

### Rewriting the program ([Model.lean](../../lean/1y-bismuth-2020-07-15/Model.lean))

`Bismuth.kt` is rewritten in Lean function by function. The parts whose Kotlin code is the same as in the version of 2019-09-29, such as array access and resizing tables, are taken from the rewrite of that version ([Model.lean of 1y-bismuth](../../lean/1y-bismuth/Model.lean)).

A Lean function must always end, so every while loop, every do-while loop and the recursion get an upper bound $`f`$ on the number of iterations and the depth; when the bound is reached, the result is "out of bound". There are four kinds of results.

| result | meaning |
|---|---|
| value | finished with a value |
| exception | Kotlin would throw (an index out of range, the first or last element of an empty array, …) |
| unsupported | a case the rewrite does not handle (running out of a bound in the parent search, which cannot happen) |
| out of bound | the bound $`f`$ was reached |

- Arrays are lists, and integers are unbounded integers.
- When the Kotlin program resizes a table without changing its width, it reuses the rows of the old table. If, in the expansion along a path, the new table has the same width as the old mountain, writing into the new table also changes the old mountain, which affects later cuts. With the bracket 0 this is always the case. The rewrite reproduces this: after every write into the new table, it copies the shared rows into the old mountain.

Item 2 of the result is stated in Lean as: for every $`n`$ with $`0 \le n \le 20`$ and every bound $`f`$, the rewritten program given $`X[n]`$ returns "out of bound".

### Showing "out of bound" for every bound ([Decide.lean](../../lean/1y-bismuth-2020-07-15/Decide.lean))

The method is the same as for the version of 2019-09-29. A function $`A`$ performs the same computation without the bound $`f`$.

- Inside the copy procedure, when the condition to continue, $`M_0(W-1) = 0`$, holds and no later round can copy anything, $`A`$ answers "infinite loop".
- That no later round copies anything is decided by $`c \le 0`$, or by the first target $`b + kc + 1`$ of round $`k`$ being at least $`W`$ (the targets move right with every round, so later rounds copy nothing either).
- For the other loops, $`A`$ uses a large fixed bound (100000 iterations) and answers "unknown" when it is exceeded.

The following two statements are proved.

1. For every input, if $`A`$ answers "infinite loop", then the rewritten program returns "out of bound" for every bound $`f`$.
2. For $`0 \le n \le 20`$, $`A`$ answers "infinite loop" on $`X`$ and $`n`$. This is checked by actually computing it in the Lean kernel (`decide +kernel`).

Handling $`n`$ symbolically would require showing symbolically that the ordinary expansion of $`D`$ (number of copies $`n+2`$) ends without an exception, which is not done here. Computing $`n \le 100`$ at once exceeded the memory limit (8 GB) of the environment used for checking.

The correspondence with the Lean code is as follows.

| name in this document | name in Lean |
|---|---|
| the rewritten program | `Bismuth2020.main` (the bound is an argument) |
| out of bound / exception / unsupported | `.div` / `.err` / `.unsup` |
| the function $`A`$ | `Bismuth2020.mainD` |
| infinite loop / unknown | `.stuck` / `.bound` |
| statement 1 | `Bismuth2020.main_div_of_stuck` |
| statement 2 | `Bismuth2020.target_stuck` |
| standardness | `Bismuth2020.std_target` |
| the result (whole theorem) | `Bismuth2020.main_theorem` |

### Checks

- **Axioms** ([Test/Axioms.lean](../../lean/Test/Axioms.lean)): `Bismuth2020.main_theorem` uses only the axioms `propext` and `Quot.sound`. Neither `sorry` (an omitted proof) nor `native_decide` (computation by compiled code) is used.
- **Differential test** ([tools/1y-bismuth-2020-07-15/difftest.sh](../../tools/1y-bismuth-2020-07-15/difftest.sh)): a separately written Python rewrite ([bismuth.py](../../tools/1y-bismuth-2020-07-15/bismuth.py)) and the Lean rewrite are given the same inputs and their results are compared. The inputs are the following 16366 cases, and all results agree: 16272 values, 82 exceptions and 12 that do not stop.
  - the 4000 sequences obtained by expansions from $`(1,2), \dots, (1,5)`$, with the brackets 0 to 3
  - the 59 sequences of the path above and a few others, with the brackets 0 to 5
- **Checking with the original program**: the original Kotlin program was not run. Kotlin's integers have 32 bits, so the actual program is expected to stop with an exception when the round $`k`$ reaches $`2^{30}`$, because the target $`q`$ goes out of range and becomes negative. Here Bismuth is treated as a notation with unbounded integers, so this does not affect the result.

```sh
git clone https://github.com/Syst3ms/Bismuth && cd Bismuth && git checkout bf7ba654
kotlinc src/io/github/syst3ms/bismuth/Bismuth.kt -include-runtime -d bismuth.jar
echo "(1,4,12,9,12,20)[1]" | timeout 60 java -jar bismuth.jar; echo exit=$?
```

## Notes

- This is non-termination of the computation of a single expansion. It is a different kind from the [examples of the BMS variants](../README-en.md), where repeating expansions produces an infinite sequence.
- The standardness path uses expansions with the bracket 0. Whether $`X`$ can be reached with brackets at least 1 only is not known: a search descending from $`(1,5)`$ was cut off because the sequences on the way became too long.
- Bismuth defines no function producing large numbers, so it is not shown that an actual large-number computation passes through $`X`$. What is shown is that among the sequences obtained by expansions from $`(1,5)`$ there is one whose expansion does not end.
