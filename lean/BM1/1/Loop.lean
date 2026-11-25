import Common.Lemmas
import Common.Rules

/-!
# BM1, example 1: the loop

`X k = (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0) ⁀ ((3,0,0)(2,1,0))^k ⁀ (3,1,0)`.

For `C = (3,1,0)` we have `t = 1` (0-indexed), and the bad root (左隣法) is
the rightmost column `m` with `m_0 < 3 ∧ m_1 < 1`.  No column of the repeated
block satisfies it, so the bad root is `(2,0,0)` (column 2) for every `k`.
Then `Δ = (1,0,0)`, and the first copy `B_1` starts with
`(3,0,0)(2,1,0)(3,1,0)`, so `X (k+1)` is a prefix of `X k [n]` for `n ≥ 1`.
-/

namespace DeadBms.BM1.Ex1

/-- `((3,0,0)(2,1,0))^k` -/
def blk : Nat → Mat
  | 0 => []
  | k + 1 => blk k ++ bm[(3,0,0)(2,1,0)]

def P : Mat := bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)]

def C : Col := [3, 1, 0]

/-- the loop family -/
def X (k : Nat) : Mat := (P ++ blk k) ++ [C]

def S (W : Mat) : Prop := ∃ k, W = X k

theorem blk_mem : ∀ k, ∀ c ∈ blk k, c = [3, 0, 0] ∨ c = [2, 1, 0]
  | 0, _, h => by simp [blk] at h
  | k + 1, c, h => by
    simp only [blk, List.mem_append] at h
    rcases h with h | h
    · exact blk_mem k c h
    · simp at h
      rcases h with h | h <;> simp [h]

theorem badRoot (k : Nat) : leftAdj (X k) 1 = some 2 := by
  rw [X, leftAdj_snoc, findLastIdx_append_none]
  · decide
  · apply findLastIdx_eq_none
    intro c hc
    rcases blk_mem k c hc with rfl | rfl <;> decide

theorem loop : Loop BM1 S 1 := by
  constructor
  · rintro _ ⟨k, rfl⟩
    simp [X]
  · rintro _ ⟨k, rfl⟩ n hn
    obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1) (A := P ++ blk k) (C := C) (t := 1) (r := 2)
      n hn (by decide) (badRoot k) (by simp [P]) bm[(2,0,0)(1,1,0)(2,1,0)] (blk k) rfl
      bm[(3,0,0)(2,1,0)(3,1,0)] rfl
    refine ⟨X (k + 1), Z, ⟨k + 1, rfl⟩, ?_⟩
    change expand BM1 ((P ++ blk k) ++ [C]) n = _
    rw [hZ]
    simp [X, blk, C]

end DeadBms.BM1.Ex1
