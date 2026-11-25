import Common.Ubim
import Common.Rules

/-!
# BM3: the loop

`X k = (0,0,0)(1,1,1)(2,1,1) ⁀ (1,1,0)(2,2,1) ⁀ (3,1,0)(4,2,1) ⁀ ⋯ ⁀ (2k-1,1,0)(2k,2,1) ⁀ (2k+1,1,1)`.

For `C = (2k+1,1,1)` we have `t = 2` (0-indexed).  Column 0 is zero, every
other column is positive in row 0 and at least `1 = c_1` in row 1, so the
bad root (上行枝無視方式) is column 0 (`ubim_eq_zero`).  Then
`Δ = (2k+1,1,0)`, and the first copy `B_1` starts with
`(2k+1,1,0)(2k+2,2,1)(2k+3,1,1)`: the BM3 flags of the first three columns are
`a'_{0y} = 1`, `a'_{1y} = 1`, `a'_{21} = 0`.  So `X (k+1)` is a prefix of
`X k [n]` for `n ≥ 1`.
-/

namespace DeadBms.BM3.Ex

def P : Mat := bm[(0,0,0)(1,1,1)(2,1,1)]

/-- `(1,1,0)(2,2,1) ⁀ ⋯ ⁀ (2k-1,1,0)(2k,2,1)` -/
def blk : Nat → Mat
  | 0 => []
  | k + 1 => blk k ++ [[2 * k + 1, 1, 0], [2 * k + 2, 2, 1]]

def C (k : Nat) : Col := [2 * k + 1, 1, 1]

/-- the loop family -/
def X (k : Nat) : Mat := (P ++ blk k) ++ [C k]

def S (W : Mat) : Prop := ∃ k, W = X k

theorem blk_mem : ∀ k, ∀ c ∈ blk k, 0 < ent c 0 ∧ 1 ≤ ent c 1
  | 0, _, h => by simp [blk] at h
  | k + 1, c, h => by
    simp only [blk, List.mem_append] at h
    rcases h with h | h
    · exact blk_mem k c h
    · simp at h
      rcases h with rfl | rfl <;> simp [ent]

theorem badRoot (k : Nat) : ubim (X k) 2 = some 0 := by
  have hlast : col (X k) ((X k).length - 1) = C k := col_last _ _
  have htail : (X k).tail = ([[1, 1, 1], [2, 1, 1]] ++ blk k) ++ [C k] := by simp [X, P]
  apply ubim_eq_zero (X k) 2 (by decide) (by simp [X, P])
  · intro y
    show ent [0, 0, 0] y = 0
    rcases y with _ | _ | _ | y <;> simp [ent]
  · intro c hc
    rw [htail] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | h) | rfl
    · decide
    · decide
    · exact (blk_mem k c h).1
    · simp [C, ent]
  · intro c hc
    rw [hlast]
    rw [htail, List.dropLast_concat] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | h
    · simp [C, ent]
    · simp [C, ent]
    · simpa [C, ent] using (blk_mem k c h).2
  · intro y h1 h2
    rw [hlast]
    rcases y with _ | _ | _ | y <;> simp [C, ent] <;> omega

theorem flags (k : Nat) (x y : Nat) (hx : x < P.length) :
    BM3.ascend ((P ++ blk k).drop 0) x y = ascBM3 P x y := by
  show ascBM3 (P ++ blk k) x y = ascBM3 P x y
  exact ascBM3_append P (blk k) x y hx

theorem first_copy (k : Nat) :
    bumpMat (BM3.ascend ((P ++ blk k).drop 0)) (delta 2 (C k) (col (P ++ blk k) 0)) 1 0 P =
      [[2 * k + 1, 1, 0], [2 * k + 2, 2, 1], [2 * k + 3, 1, 1]] := by
  rw [bumpMat_congr _ (ascBM3 P) _ _ 0 P (fun x' _ h2 => funext fun y => flags k x' y (by simpa using h2))]
  have h00 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 0 0 = true := by decide
  have h01 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 0 1 = true := by decide
  have h10 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 1 0 = true := by decide
  have h11 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 1 1 = true := by decide
  have h20 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 2 0 = true := by decide
  have h21 : ascBM3 [[0, 0, 0], [1, 1, 1], [2, 1, 1]] 2 1 = false := by decide
  have hc : col (P ++ blk k) 0 = [0, 0, 0] := rfl
  rw [hc]
  simp [P, C, bumpMat, bumpCol, delta, ent, h00, h01, h10, h11, h20, h21]
  omega

theorem loop : Loop BM3 S 1 := by
  constructor
  · rintro _ ⟨k, rfl⟩
    simp [X]
  · rintro _ ⟨k, rfl⟩ n hn
    obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM3) (A := P ++ blk k) (C := C k) (t := 2) (r := 0)
      n hn rfl (badRoot k) (by simp [P]) P (blk k) rfl _ (first_copy k)
    refine ⟨X (k + 1), Z, ⟨k + 1, rfl⟩, ?_⟩
    change expand BM3 ((P ++ blk k) ++ [C k]) n = _
    rw [hZ]
    simp [X, blk, C]
    omega

end DeadBms.BM3.Ex
