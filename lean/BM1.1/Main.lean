import «BM1.1».Standard
import «BM1.1».Loop
import Common.Pad

/-!
# BM1.1: main theorem

`M = (0,0,0)(1,1,1)(2,0,0)(1,1,1)` is standard in BM1.1, and for every bracket
`n ≥ 1` the computation of `M[n]` never reaches the empty matrix (also with
the zero row of the standardness path appended).  `M` also has an infinite
descending sequence of expansions.
-/

namespace DeadBms.BM1_1.Ex

theorem uniform : Uniform 3 M := by decide

theorem mem_S : S M := ⟨0, Or.inl (by decide)⟩

theorem f_ge (n : Nat) (hn : 1 ≤ n) : 1 ≤ BM1_1.f n := by
  simpa [BM1_1] using Nat.mul_le_mul hn hn

theorem main :
    Std BM1_1 M ∧
    (∀ n, 1 ≤ n → ¬ Halts BM1_1 M n) ∧
    (∀ n, 1 ≤ n → ¬ Halts BM1_1 (padM 4 M) n) ∧
    ¬ Acc (fun B A => Step BM1_1 A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step BM1_1 (seq i) (seq (i + 1))) := by
  refine ⟨std, fun n hn => loop.not_halts f_ge M mem_S n hn, fun n hn => ?_,
    loop.not_acc M mem_S, loop.infinite_descent M mem_S⟩
  rw [halts_padM BM1_1_padInv 4 uniform]
  exact loop.not_halts f_ge M mem_S n hn

end DeadBms.BM1_1.Ex
