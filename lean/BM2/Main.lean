import BM2.Standard
import BM2.Loop
import Common.Pad

/-!
# BM2: main theorem

`M = (0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)` is standard in BM2, and for every bracket
`n ≥ 1` the computation of `M[n]` never reaches the empty matrix (also with
the zero row of the standardness path appended).  `M` also has an infinite
descending sequence of expansions.
-/

namespace DeadBms.BM2.Ex

theorem uniform : Uniform 4 M := by decide

theorem mem_S : S M := ⟨0, by decide⟩

theorem f_ge (n : Nat) (hn : 1 ≤ n) : 1 ≤ BM2.f n := by
  simpa [BM2] using Nat.mul_le_mul hn hn

theorem main :
    Std BM2 M ∧
    (∀ n, 1 ≤ n → ¬ Halts BM2 M n) ∧
    (∀ n, 1 ≤ n → ¬ Halts BM2 (padM 5 M) n) ∧
    ¬ Acc (fun B A => Step BM2 A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step BM2 (seq i) (seq (i + 1))) := by
  refine ⟨std, fun n hn => loop.not_halts f_ge M mem_S n hn, fun n hn => ?_,
    loop.not_acc M mem_S, loop.infinite_descent M mem_S⟩
  rw [halts_padM BM2_padInv 5 uniform]
  exact loop.not_halts f_ge M mem_S n hn

end DeadBms.BM2.Ex
