import «BM1.1».Main

/-!
# BM2.1: main theorem

BM2.1 has the expansion rules of BM1.1 (上行枝無視方式, 全枝有効方式, 改変なし)
and `f(n) = n + 1`; the page says "BM1.1と同じ".  So the example of BM1.1
(hyp cos) applies.
-/

namespace DeadBms.BM2_1.Ex

theorem expand_eq (M : Mat) (n : Nat) : expand BM2_1 M n = expand BM1_1 M n := rfl

/-- the example: `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` -/
def M : Mat := BM1_1.Ex.M

theorem loop : Loop BM2_1 BM1_1.Ex.S 1 := Loop.of_expand_eq expand_eq BM1_1.Ex.loop

theorem f_ge (n : Nat) (_ : 1 ≤ n) : 1 ≤ BM2_1.f n := by simp [BM2_1]

theorem main :
    Std BM2_1 M ∧
    (∀ n, 1 ≤ n → ¬ Halts BM2_1 M n) ∧
    (∀ n, 1 ≤ n → ¬ Halts BM2_1 (padM 4 M) n) ∧
    ¬ Acc (fun B A => Step BM2_1 A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step BM2_1 (seq i) (seq (i + 1))) := by
  refine ⟨Std.of_expand_eq expand_eq BM1_1.Ex.std,
    fun n hn => loop.not_halts f_ge M BM1_1.Ex.mem_S n hn, fun n hn => ?_,
    loop.not_acc M BM1_1.Ex.mem_S, loop.infinite_descent M BM1_1.Ex.mem_S⟩
  show ¬ Halts BM2_1 (padM 4 BM1_1.Ex.M) n
  rw [halts_padM BM2_1_padInv 4 BM1_1.Ex.uniform]
  exact loop.not_halts f_ge M BM1_1.Ex.mem_S n hn

end DeadBms.BM2_1.Ex
