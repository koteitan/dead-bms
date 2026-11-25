import «1y-bismuth».Decide
import «1y-bismuth».Standard

/-!
# Main theorem: Bismuth (2019-09-29) does not terminate

`(1,2,4,7,5,4,5,10)` is standard (reached from `(1,3)`), and for every bracket
`n` with `1 ≤ n ≤ 20` the program runs forever on `(1,2,4,7,5,4,5,10)[n]`:
`main fuel target n = div` for every `fuel`.

The computation stops making progress at the same place for every `n`.  The
terms (mountain, path, step, distance table, copy procedure) are defined in
`doc/1y-bismuth/README-en.md`.

1. The bottom-right value of the mountain of `S` is 3, so `S[n]` is an
   expansion along a path.  The path records `D = (1,1,1,0,0,3)`, and `D[n+2]`
   is computed.
2. `D[n+2]` is again an expansion along a path.  Its path records
   `D' = (1,1,1,0,0,0,2)` with the steps `→ → → → ↓0 →`, and `D'[n+4]` (an
   ordinary expansion) ends.
3. Back in `D[n+2]`, the step `↓0` cuts the piece `((0),(0))` (2 rows,
   1 column) out of the distance table, and the copy procedure widens it to
   width `3(n+4)`.  There are no columns to copy, so the last entry of the
   first row stays 0 forever.

Only the width `3(n+4)` depends on `n`.  For `n ≤ 20` the theorem is checked by
`mainD`, which computes without a bound and answers `stuck` at this point.
-/

namespace Bismuth

theorem target_stuck : ∀ n : Nat, n < 20 → mainD 5 target ((n : Int) + 1) = .stuck := by
  decide +kernel

/-- **Bismuth (2019-09-29) does not terminate**: the standard sequence
`(1,2,4,7,5,4,5,10)` makes the program run forever for every bracket `1 ≤ n ≤ 20` -/
theorem main_theorem :
    Std target ∧ ∀ n : Nat, 1 ≤ n → n ≤ 20 → ∀ fuel, main fuel target n = .div := by
  refine ⟨std_target, fun n h1 h2 fuel => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := target_stuck k (by omega)
  have hk : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
  rw [hk]
  exact main_div_of_stuck 5 target _ h fuel

end Bismuth
