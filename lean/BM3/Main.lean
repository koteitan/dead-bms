import BM3.Standard
import BM3.Loop
import Common.Pad

/-!
# BM3: main theorem

`M = (0,0,0)(1,1,1)(2,1,1)(1,1,1)` is standard in BM3, and for every bracket
`n ≥ 1` the computation of `M[n]` never reaches the empty matrix (also with
the zero row of the standardness path appended).  `M` also has an infinite
descending sequence of expansions.
-/

namespace DeadBms.BM3.Ex

theorem uniform : Uniform 3 M := by decide

theorem mem_S : S M := ⟨0, by decide⟩

theorem f_ge (n : Nat) (hn : 1 ≤ n) : 1 ≤ BM3.f n := by
  simpa [BM3] using Nat.mul_le_mul hn hn

theorem main :
    Std BM3 M ∧
    (∀ n, 1 ≤ n → ¬ Halts BM3 M n) ∧
    (∀ n, 1 ≤ n → ¬ Halts BM3 (padM 4 M) n) ∧
    ¬ Acc (fun B A => Step BM3 A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step BM3 (seq i) (seq (i + 1))) := by
  refine ⟨std, fun n hn => loop.not_halts f_ge M mem_S n hn, fun n hn => ?_,
    loop.not_acc M mem_S, loop.infinite_descent M mem_S⟩
  rw [halts_padM BM3_padInv 4 uniform]
  exact loop.not_halts f_ge M mem_S n hn

end DeadBms.BM3.Ex
