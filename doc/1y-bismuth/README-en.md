[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Non-termination of Bismuth (version of 2019-09-29)

## Bismuth

Bismuth is a Y-sequence-like notation by Syst3ms ([User blog:Syst3ms/Bismuth : not Y sequence, but close](https://googology.fandom.com/wiki/User_blog:Syst3ms/Bismuth_:_not_Y_sequence,_but_close)). The blog post does not describe the expansion rules; the definition is the Kotlin program [Syst3ms/Bismuth](https://github.com/Syst3ms/Bismuth) itself.

The version treated here is the commit [`5e4c65c3`](https://github.com/Syst3ms/Bismuth/blob/5e4c65c3/src/io/github/syst3ms/bismuth/Bismuth.kt) of 2019-09-29 ("Fixed small expansion quick").

The expansion of a sequence $`X`$ with bracket $`t`$ is written $`X[t]`$.

## Result

Let $`S = (1,2,4,7,5,4,5,10)`$. The following is proved in Lean (`Bismuth.main_theorem` in [Main.lean](../../lean/1y-bismuth/Main.lean)).

1. $`S`$ is standard: it is obtained from $`(1,3)`$ by 19 expansions with brackets at least 1.
2. For every $`n`$ with $`1 \le n \le 20`$, the computation of $`S[n]`$ by the program does not end.

The case $`n \gt 20`$ is not proved.

## Standardness

Expanding $`(1,3)`$ with the following brackets gives $`S`$ ([Standard.lean](../../lean/1y-bismuth/Standard.lean), checked by computation in Lean).

```
    (1,3)
[2] (1,2,4,8)
[3] (1,2,4,7,11)
[2] (1,2,4,7,10)
[2] (1,2,4,7,9,12)
[1] (1,2,4,7,9)
[2] (1,2,4,7,8,10,13)
[1] (1,2,4,7,8,10)
[1] (1,2,4,7,8)
[2] (1,2,4,7,7)
[2] (1,2,4,7,6,9)
[1] (1,2,4,7,6)
[2] (1,2,4,7,5,7,10)
[1] (1,2,4,7,5,7)
[2] (1,2,4,7,5,6)
[2] (1,2,4,7,5,5)
[2] (1,2,4,7,5,4,7,5)
[1] (1,2,4,7,5,4,7)
[2] (1,2,4,7,5,4,6)
[2] (1,2,4,7,5,4,5,10)
```

## The expansion rules

This section gives the part of the expansion rules, as read from the program, that this example uses. Positions and rows are counted from 0.

### Mountain

From a sequence $`X = (X_0, \dots, X_{L-1})`$, rows $`V_0, V_1, \dots`$ (each of length $`L`$) and parents $`P_r(i)`$ are determined as follows. This table is called the mountain.

- $`V_0 = X`$.
- The parent $`P_r(i)`$ of position $`i`$ in row $`r`$ is the largest $`j`$ satisfying the following two conditions. If there is no such $`j`$, then $`i`$ has no parent in row $`r`$.
  - $`j \lt i`$ and $`0 \lt V_r(j) \lt V_r(i)`$
  - if $`r \ge 1`$, then $`j \le P_{r-1}(i)`$
- $`V_{r+1}(i) = V_r(i) - V_r(P_r(i))`$. If $`i`$ has no parent in row $`r`$, then $`V_{r+1}(i) = 0`$.
- Rows are added as long as the last position $`L-1`$ has a parent in the lowest row. The last row is $`V_R`$.

Two more things are determined.

- The distance to the parent $`O_r(i) = i - P_r(i)`$. If $`i`$ has no parent in row $`r`$, then $`O_r(i) = 0`$. The table of $`O_0, \dots, O_R`$ is called the distance table.
- The bad root $`b = P_{R-1}(L-1)`$.

### Two cases

The computation of $`X[t]`$ depends on the bottom-right value $`V_R(L-1)`$ of the mountain.

- If $`V_R(L-1) \le 1`$ (ordinary expansion): the part from the bad root $`b`$ to position $`L-2`$ is repeated $`t`$ times. How the values are set while repeating does not matter for why this example does not stop, so it is omitted here. On the way, the distance table is widened to width $`b + (L-1-b)t + 1`$ by the copy procedure (next subsection).
- If $`V_R(L-1) \ge 2`$: the expansion along a path (the subsection after next) is used.

### Copy procedure

This procedure widens a table $`M`$ with $`h`$ rows and $`w`$ columns (rows $`M_0, \dots, M_{h-1}`$) to width $`W`$.

1. Let $`b_M = (w-1) - M_{h-2}(w-1)`$ and $`c = w - 1 - b_M`$. $`c`$ is the number of columns to the right of $`b_M`$.
2. Append zeros to every row to make $`W`$ columns.
3. While the last entry $`M_0(W-1)`$ of the first row is 0, repeat the following for $`k = 1, 2, 3, \dots`$ in order.
   - Copy columns $`b_M+1, \dots, b_M+c`$ to columns $`b_M+kc+1, \dots, b_M+(k+1)c`$ (columns at $`W`$ or beyond are not written).

### Expansion along a path

If $`V_R(L-1) \ge 2`$, $`X[t]`$ is computed as follows.

1. Take a path on the mountain. Start at (row 0, position 0) and move right or down. At (row $`r`$, position $`x`$):
   - Record $`V_r(x)`$.
   - If $`V_{r+1}(x+1) \gt 0`$, move down to (row $`r+1`$, position $`x'`$). Here $`x'`$ is the largest position whose parent in row $`r`$ is $`x`$. If there is no such position and $`x`$ itself has no parent in row $`r`$, then $`x' = x`$ (otherwise the program throws an exception). This step is written $`{\downarrow}(x'-x)`$. If row $`r+1`$ does not exist or $`x+1 = L`$, $`V_{r+1}(x+1)`$ is taken to be 0.
   - Otherwise move right to (row $`r`$, position $`x+1`$). This step is written $`{\rightarrow}`$.
   - Stop when the position becomes $`L`$. The last step is discarded.

   Let $`D`$ be the recorded sequence and $`\sigma_0, \dots, \sigma_{m-1}`$ the steps.
2. Compute $`D[t+2]`$ by the same rules. Let $`b_D`$ be the bad root of $`D`$.
3. Build a new list of steps: $`\sigma_0, \dots, \sigma_{b_D-1}`$ followed by $`\sigma_{b_D}, \dots, \sigma_{m-1}`$ repeated $`t+1`$ times. The width $`W`$ of the new table is 1 plus the total rightward movement of the new steps. $`{\rightarrow}`$ moves right by 1, and $`{\downarrow}k`$ moves right by $`k`$.
4. Process the new steps from the first one. For each step, cut the rectangle that the step spans in the old mountain (1 row by 2 columns for $`{\rightarrow}`$, 2 rows by $`k+1`$ columns for $`{\downarrow}k`$) out of the mountain and the distance table, and paste it into the new table. For a step $`{\downarrow}k`$, the piece cut out of the distance table is first widened to width $`W`$ by the copy procedure.

How the values are pasted and the final step do not matter for why this example does not stop, so they are omitted here.

## Why S[n] does not stop

The computation of $`S[n]`$ stops making progress at the same place for every $`n`$.

### Level 1: S[n]

The mountain of $`S`$ is as follows (`-` means that there is no parent).

```
position  0  1  2  3  4  5  6  7
V_0       1  2  4  7  5  4  5 10
V_1       0  1  2  3  1  2  1  5
V_2       0  0  1  1  0  1  0  4
V_3       0  0  0  0  0  0  0  3

P_0       -  0  1  2  2  1  5  6
P_1       -  -  1  2  -  1  -  6
P_2       -  -  -  -  -  -  -  5
```

$`R = 3`$ and $`V_3(7) = 3 \ge 2`$, so the expansion along a path is used. The path is as follows.

| (row, position) | recorded value | move | step |
|---|---|---|---|
| (0, 0) | `V_0(0) = 1` | `V_1(1) = 1 > 0`, so down. In row 0 only position 1 has parent 0, so to (1, 1) | ↓1 |
| (1, 1) | `V_1(1) = 1` | `V_2(2) = 1 > 0`, so down. In row 1 positions 2 and 5 have parent 1, so to (2, 5) | ↓4 |
| (2, 5) | `V_2(5) = 1` | `V_3(6) = 0`, so right | → |
| (2, 6) | `V_2(6) = 0` | `V_3(7) = 3 > 0`, so down. In row 2 no position has parent 6, and 6 has no parent in row 2, so to (3, 6) | ↓0 |
| (3, 6) | `V_3(6) = 0` | there is no row 4, so right | → |
| (3, 7) | `V_3(7) = 3` | right. The position becomes 8 and the path ends | → (discarded) |

The recorded sequence is $`D = (1,1,1,0,0,3)`$. Next, $`D[n+2]`$ is computed.

### Level 2: D[n+2] (D = (1,1,1,0,0,3))

```
position  0  1  2  3  4  5
V_0       1  1  1  0  0  3
V_1       0  0  0  0  0  2

P_0       -  -  -  -  -  2
O_0       0  0  0  0  0  3
O_1       0  0  0  0  0  0
```

$`R = 1`$ and $`V_1(5) = 2 \ge 2`$, so this is again an expansion along a path. The path is as follows.

| (row, position) | recorded value | move | step |
|---|---|---|---|
| (0, 0) | `V_0(0) = 1` | `V_1(1) = 0`, so right | → |
| (0, 1) | `V_0(1) = 1` | `V_1(2) = 0`, so right | → |
| (0, 2) | `V_0(2) = 1` | `V_1(3) = 0`, so right | → |
| (0, 3) | `V_0(3) = 0` | `V_1(4) = 0`, so right | → |
| (0, 4) | `V_0(4) = 0` | `V_1(5) = 2 > 0`, so down. In row 0 no position has parent 4, and 4 has no parent in row 0, so to (1, 4) | ↓0 |
| (1, 4) | `V_1(4) = 0` | there is no row 2, so right | → |
| (1, 5) | `V_1(5) = 2` | right. The position becomes 6 and the path ends | → (discarded) |

The recorded sequence is $`D' = (1,1,1,0,0,0,2)`$, and the steps are $`({\rightarrow},{\rightarrow},{\rightarrow},{\rightarrow},{\downarrow}0,{\rightarrow})`$. Next, $`D'[n+4]`$ is computed.

### Level 3: D'[n+4] (D' = (1,1,1,0,0,0,2))

```
position  0  1  2  3  4  5  6
V_0       1  1  1  0  0  0  2
V_1       0  0  0  0  0  0  1

P_0       -  -  -  -  -  -  2
O_0       0  0  0  0  0  0  4
O_1       0  0  0  0  0  0  0
```

$`V_1(6) = 1`$, so this is an ordinary expansion, with bad root $`P_0(6) = 2`$. This expansion ends, and $`D'[n+4]`$ is $`(1,1)`$ followed by $`(1,0,0,0)`$ repeated $`n+4`$ times.

On the way, the distance table is widened by the copy procedure, with $`b_M = 6 - O_0(6) = 2`$ and $`c = 4`$. For $`n = 2`$ the width is $`W = 27`$, and the first row changes as follows.

```
start    0 0 0 0 0 0 4  0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0
round 1  0 0 0 0 0 0 4  0 0 0 4  0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0
round 2  0 0 0 0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 0  0 0 0 0  0 0 0 0
round 3  0 0 0 0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 0  0 0 0 0
round 4  0 0 0 0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 0
round 5  0 0 0 0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4  0 0 0 4
```

Each round copies $`(0,0,0,4)`$ from columns 3 to 6 further to the right. After round 5 the last entry is 4, so the procedure ends.

### Back to level 2

The bad root of $`D'`$ is 2, so the new list of steps is as follows.

```math
{\rightarrow}\ {\rightarrow}\ ({\rightarrow}\ {\rightarrow}\ {\downarrow}0\ {\rightarrow})^{n+3}
```

Here $`(\cdots)^{n+3}`$ means the contents of the parentheses repeated $`n+3`$ times. The width of the new table is $`W = 1 + 2 + 3(n+3) = 3(n+4)`$.

The new steps are processed from the first one. Steps 0 to 3 are $`{\rightarrow}`$, which are only cut and pasted. Step 4 is $`{\downarrow}0`$, the step from (0, 4) to (1, 4) of the old path. Cutting rows 0 to 1 and column 4 out of the distance table gives the table with 2 rows and 1 column

```math
M = \begin{pmatrix} O_0(4) \cr O_1(4) \end{pmatrix} = \begin{pmatrix} 0 \cr 0 \end{pmatrix}
```

which is widened to width $`W`$ by the copy procedure. Since $`h = 2`$ and $`w = 1`$, $`b_M = 0 - M_0(0) = 0`$ and $`c = 1 - 1 - 0 = 0`$: there are no columns to copy. For $`n = 2`$ ($`W = 18`$) the first row is as follows.

```
start    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0   last entry is 0, so continue
round 1  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0   nothing to copy; last entry is 0, so continue
round 2  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0   nothing to copy; last entry is 0, so continue
round 3  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0   nothing to copy; last entry is 0, so continue
…
```

The table never changes and the last entry stays 0, so the repetition never ends. Hence the computation of $`D[n+2]`$ does not end, and neither does that of $`S[n]`$.

Only the width $`W = 3(n+4)`$ depends on $`n`$, and the same happens for every $`n`$.

In general, processing a step $`{\downarrow}0`$ in step 4 of the expansion along a path never ends. The starting position $`x`$ of a step $`{\downarrow}0`$ has no parent in row $`r`$, so the first row of the piece is $`(0)`$, which gives $`b_M = 0`$ and $`c = 0`$. The path of level 1 also contains $`{\downarrow}0`$, but the computation stops making progress at level 2 before reaching it.

A Python rewrite of the later version of 2019-10-19 (commit `2213d83a`) does not run forever on the same input: it throws an exception instead (taking the last element of an empty list). That version is not formalized.

## How it is formalized

### Rewriting the program ([Model.lean](../../lean/1y-bismuth/Model.lean))

`Bismuth.kt` is rewritten in Lean function by function. A Lean function must always end, so every while loop and the recursion get an upper bound $`f`$ on the number of iterations and the depth; when the bound is reached, the result is "out of bound". There are four kinds of results.

| result | meaning |
|---|---|
| value | finished with a value |
| exception | Kotlin would throw (an index out of range, the first or last element of an empty array, …) |
| unsupported | because of Kotlin's array sharing (below), the rewrite could differ from the program |
| out of bound | the bound $`f`$ was reached |

- Arrays are lists, and integers are unbounded integers (the numbers in these computations are small).
- When the Kotlin program resizes a table without changing its width, it reuses the rows of the old table. So if, in step 4 of the expansion along a path, the new table has the same width as the old mountain, writing into the new table also changes the old mountain. The rewrite returns "unsupported" in that case. It does not happen in the computations of the theorem.

Item 2 of the result is stated in Lean as: for every $`n`$ with $`1 \le n \le 20`$ and every bound $`f`$, the rewritten program given $`S[n]`$ returns "out of bound". If the Kotlin program ended after finitely many iterations, the rewrite would return something other than "out of bound" for every $`f`$ at least that number. Since the result is "out of bound" for every $`f`$, the Kotlin program does not end.

### Showing "out of bound" for every bound ([Decide.lean](../../lean/1y-bismuth/Decide.lean))

A function $`A`$ performs the same computation without the bound $`f`$. Inside the copy procedure, when the condition to continue, $`M_0(W-1) = 0`$, holds and no later round can copy anything, $`A`$ answers "infinite loop". That no later round copies anything is decided by $`c \le 0`$, or by the first target column $`b_M + kc + 1`$ of round $`k`$ being at least $`W`$ (the targets move right with every round, so later rounds copy nothing either). For the other while loops, $`A`$ uses a large fixed bound (100000 iterations) and answers "unknown" when it is exceeded.

The following two statements are proved.

1. For every input, if $`A`$ answers "infinite loop", then the rewritten program returns "out of bound" for every bound $`f`$. This is shown by comparing $`A`$ with the rewritten program, following the structure of the program.
2. For $`1 \le n \le 20`$, $`A`$ answers "infinite loop" on $`S`$ and $`n`$. This is checked by actually computing it in the Lean kernel (`decide +kernel`, about 20 seconds).

Handling $`n`$ symbolically would require following the ordinary expansion of level 3 (bracket $`n+4`$) symbolically, which is not done here. Computing $`n \le 100`$ at once exceeded the memory limit (8 GB) of the environment used for checking.

The correspondence with the Lean code is as follows.

| name in this document | name in Lean |
|---|---|
| the rewritten program | `Bismuth.main` (the bound is an argument) |
| out of bound / exception / unsupported | `.div` / `.err` / `.unsup` |
| the function $`A`$ | `Bismuth.mainD` |
| infinite loop / unknown | `.stuck` / `.bound` |
| statement 1 | `Bismuth.main_div_of_stuck` |
| statement 2 | `Bismuth.target_stuck` |
| standardness | `Bismuth.std_target` |
| the result (whole theorem) | `Bismuth.main_theorem` |

### Checks

- **Axioms** ([Test/Axioms.lean](../../lean/Test/Axioms.lean)): `Bismuth.main_theorem` uses only the axioms `propext` and `Quot.sound`. Neither `sorry` (an omitted proof) nor `native_decide` (computation by compiled code) is used.
- **Differential test** ([tools/1y-bismuth/difftest.sh](../../tools/1y-bismuth/difftest.sh)): a separately written Python rewrite ([bismuth.py](../../tools/1y-bismuth/bismuth.py)) and the Lean rewrite are given the same inputs and their results are compared. The inputs are 12000 pairs of the 4000 sequences obtained by expansions from $`(1,2), \dots, (1,5)`$ and the brackets 1 to 3; all results agree.
- **Checking with the original program**: the original Kotlin program was not run. To check, run the following and see `exit=124` (stopped after 60 seconds).

```sh
git clone https://github.com/Syst3ms/Bismuth && cd Bismuth && git checkout 5e4c65c3
kotlinc src/io/github/syst3ms/bismuth/Bismuth.kt -include-runtime -d bismuth.jar
echo "(1,2,4,7,5,4,5,10)[2]" | timeout 60 java -jar bismuth.jar; echo exit=$?
```

## Notes

- This is non-termination of the computation of a single expansion. It is a different kind from the [examples of the BMS variants](../README-en.md), where repeating expansions produces an infinite sequence.
- Bismuth defines no function producing large numbers, so it is not shown that an actual large-number computation passes through $`S`$. What is shown is that among the sequences obtained by expansions from $`(1,3)`$ there is one whose expansion does not end.
