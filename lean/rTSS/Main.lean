import BM1.«1».Main

/-!
# rTSS: main theorem

rTSS has the rules of BM1 (左隣法, 全枝有効方式, 改変なし, `f(n) = n²`) on
trio (3-row) matrices; the page says "BM1のトリオ数列システムと同じ".  So the
3-row example of BM1 (hyp cos) applies: it is reached from
`(0,0,0)(1,1,1)(2,2,2)` by 3-row expansions, and its computation does not
halt.
-/

namespace DeadBms.rTSS.Ex

theorem rTSS_eq : rTSS = BM1 := rfl

/-- the example: `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` -/
def M : Mat := BM1.Ex1.M

/-- `(0,0,0)(1,1,1)(2,2,2)` -/
def start : Mat := bm[(0,0,0)(1,1,1)(2,2,2)]

/-- the brackets from `(0,0,0)(1,1,1)(2,2,2)` -/
def path : List Nat := [1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 2]

theorem path_eq : runList rTSS start path = M := by decide

theorem main :
    runList rTSS start path = M ∧
    Std rTSS M ∧
    (∀ n, 1 ≤ n → ¬ Halts rTSS M n) ∧
    ¬ Acc (fun B A => Step rTSS A B) M ∧
    (∃ seq : Nat → Mat, seq 0 = M ∧ ∀ i, Step rTSS (seq i) (seq (i + 1))) := by
  rw [rTSS_eq]
  obtain ⟨h1, h2, _, h4, h5⟩ := BM1.Ex1.main
  exact ⟨path_eq, h1, h2, h4, h5⟩

end DeadBms.rTSS.Ex
