import «1y-bismuth-2020-07-15».Decide
import «1y-bismuth-2020-07-15».Standard

/-!
# Main theorem: Bismuth (2020-07-15) does not terminate

`X = (1,4,12,9,12,20)` is standard (reached from `(1,5)` with the brackets 0
and 1), and for every bracket `n` with `0 ≤ n ≤ 20` the program runs forever on
`X[n]`: `main fuel target n = div` for every `fuel`.

The computation stops making progress at the same place for every `n`.  The
terms (mountain, path, distance table, copy procedure) are explained in
`doc/1y-bismuth-2020-07-15/README-en.md`.

1. The bottom-right value of the mountain of `X` is at least 2, so `X[n]` is an
   expansion along a path.  The path records `D`, and `D[n+1]` (an ordinary
   expansion) ends; its bad root is 3.
2. The bad part of the distance table is the row `(0, 0, 0)` (one row, three
   columns).  The copy procedure widens it to width `2n+3`, copying its columns
   1 and 2 to the right.  All the copied values are 0, so the last entry of the
   row stays 0 and the loop never ends.

Only the width `2n+3` depends on `n`.  For `n ≤ 20` the theorem is checked by
`mainD`, which computes without a bound and answers `stuck` at this point.
-/

namespace Bismuth2020

theorem target_stuck : ∀ n : Nat, n ≤ 20 → mainD 5 target (n : Int) = .stuck := by
  decide +kernel

/-- **Bismuth (2020-07-15) does not terminate**: the standard sequence
`(1,4,12,9,12,20)` makes the program run forever for every bracket `0 ≤ n ≤ 20` -/
theorem main_theorem :
    Std target ∧ ∀ n : Nat, n ≤ 20 → ∀ fuel, main fuel target n = .div :=
  ⟨std_target, fun n hn fuel => main_div_of_stuck 5 target n (target_stuck n hn) fuel⟩

end Bismuth2020
