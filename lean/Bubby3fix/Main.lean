import «BM1.1».Main

/-!
# Bubby3's fix: main theorem

Bubby3's fix has exactly the rules of BM1.1 (上行枝無視方式, 全枝有効方式,
改変なし, `f(n) = n²`); the page says "BM1.1と同じ".  So the example of BM1.1
(hyp cos) applies.
-/

namespace DeadBms.Bubby3fix.Ex

theorem Bubby3fix_eq : Bubby3fix = BM1_1 := rfl

/-- the example: `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` -/
def M : Mat := BM1_1.Ex.M

theorem main :
    Std Bubby3fix M ∧
    (∀ n, 1 ≤ n → ¬ Halts Bubby3fix M n) ∧
    (∀ n, 1 ≤ n → ¬ Halts Bubby3fix (padM 4 M) n) ∧
    ¬ Acc (fun B A => Step Bubby3fix A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step Bubby3fix (seq i) (seq (i + 1))) := by
  rw [Bubby3fix_eq]
  exact BM1_1.Ex.main

end DeadBms.Bubby3fix.Ex
