import Common.Ubim
import Common.Rules

/-!
# BM2: the loop

`X k = P ⁀ D_0 ⁀ ⋯ ⁀ D_{k-1} ⁀ (7+6k, 3+2k, 1, 1)` with
`P = (0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)` and
`D_j = D_0 + (6j, 2j, 0, 0)`,
`D_0 = (7,3,1,0)(8,4,2,1)(9,5,2,1)(10,6,2,1)(11,5,0,0)(12,4,1,1)`.

For `C = (7+6k,3+2k,1,1)` we have `t = 3` (0-indexed), and the bad root
(上行枝無視方式) is column 0:

* row 0 strictly increases, so the row-0 ancestors of `C` are all columns,
  and the row-1 parent of a column is the rightmost column left of it with a
  smaller row-1 entry;
* every column `a ≠ 0` with a zero row-2 entry is followed by a column that
  is not larger in row 1, so it is never such a parent; hence every row-1
  ancestor of `C` other than column 0 has row-2 entry `≥ 1 = c_2`;
* so the row-2 parent of `C` is column 0, and so is the row-3 parent.

Then `Δ = (7+6k, 3+2k, 1, 0)` and the first copy `B_1` starts with
`P + A ⊗ Δ = D_k ⁀ (7+6(k+1), 3+2(k+1), 1, 1)`, so `X (k+1)` is a prefix of
`X k [n]` for `n ≥ 1`.
-/

namespace DeadBms.BM2.Ex

def P : Mat := bm[(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)]

def D (k : Nat) : Mat :=
  [[7 + 6 * k, 3 + 2 * k, 1, 0], [8 + 6 * k, 4 + 2 * k, 2, 1], [9 + 6 * k, 5 + 2 * k, 2, 1],
   [10 + 6 * k, 6 + 2 * k, 2, 1], [11 + 6 * k, 5 + 2 * k, 0, 0], [12 + 6 * k, 4 + 2 * k, 1, 1]]

/-- `D_0 ⁀ ⋯ ⁀ D_{k-1}` -/
def blk : Nat → Mat
  | 0 => []
  | k + 1 => blk k ++ D k

def C (k : Nat) : Col := [7 + 6 * k, 3 + 2 * k, 1, 1]

/-- the loop family -/
def X (k : Nat) : Mat := (P ++ blk k) ++ [C k]

def S (W : Mat) : Prop := ∃ k, W = X k

/-- the relation between adjacent columns -/
def R (a b : Col) : Prop :=
  ent a 0 < ent b 0 ∧ (ent a 2 = 0 → 0 < ent a 0 → ent b 1 ≤ ent a 1)

theorem len_blk : ∀ k, (blk k).length = 6 * k
  | 0 => rfl
  | k + 1 => by simp [blk, len_blk k, D]; omega

theorem len_pre (k : Nat) : (P ++ blk k).length = 7 + 6 * k := by
  simp [P, len_blk]; omega

theorem getLast_pre : ∀ k, (P ++ blk k).getLast? = some [6 + 6 * k, 2 + 2 * k, 1, 1]
  | 0 => rfl
  | k + 1 => by
    rw [blk, ← List.append_assoc]
    simp [List.getLast?_append, D] <;> omega

theorem adj_D (k : Nat) : Adj R (D k) := by
  simp [Adj, D, R, ent] <;> omega

theorem adj_pre : ∀ k, Adj R (P ++ blk k)
  | 0 => by simp [Adj, R, P, blk, ent]
  | k + 1 => by
    rw [blk, ← List.append_assoc]
    refine adj_append R _ _ (adj_pre k) (adj_D k) ?_
    intro a b ha hb
    rw [getLast_pre] at ha
    simp [D] at hb
    cases ha; cases hb
    simp [R, ent] <;> omega

theorem adj_X (k : Nat) : Adj R (X k) := by
  refine adj_append R _ _ (adj_pre k) trivial ?_
  intro a b ha hb
  rw [getLast_pre] at ha
  simp at hb
  cases ha; cases hb
  simp [R, C, ent] <;> omega

theorem blk_row1 : ∀ k, ∀ c ∈ blk k, 1 ≤ ent c 1
  | 0, _, h => by simp [blk] at h
  | k + 1, c, h => by
    simp only [blk, List.mem_append] at h
    rcases h with h | h
    · exact blk_row1 k c h
    · simp [D] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ent] <;> omega

theorem tail_row1 (k : Nat) : ∀ c ∈ (X k).tail, 1 ≤ ent c 1 := by
  intro c hc
  have : (X k).tail = (P.tail ++ blk k) ++ [C k] := by simp [X, P]
  rw [this] at hc
  simp only [List.mem_append, P, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | h) | rfl
  all_goals first | decide | exact blk_row1 k c h | (simp [C, ent]; omega)

theorem badRoot (k : Nat) : ubim (X k) 3 = some 0 := by
  have hlen : (X k).length = 8 + 6 * k := by
    rw [X, List.length_append, len_pre, List.length_singleton]; omega
  have hlast : col (X k) (7 + 6 * k) = C k := by
    have := col_snoc (P ++ blk k) (C k)
    rwa [len_pre] at this
  have hcol0 : col (X k) 0 = [0, 0, 0, 0] := rfl
  have hadj := adj_col R (X k) (adj_X k)
  -- row 0 is positive right of column 0 and strictly increases
  have hpos : ∀ x, 0 < x → x < (X k).length → 0 < ent (col (X k) x) 0 := by
    intro x h1 h2
    have := (hadj (x - 1) (by omega)).1
    rw [Nat.sub_add_cancel h1] at this
    omega
  have hinc : ∀ x, 0 < x → x ≤ 7 + 6 * k → parent (X k) 0 x = some (x - 1) := by
    intro x h1 h2
    apply parent0_of_prev (X k) x h1 (by omega)
    have := (hadj (x - 1) (by omega)).1
    rwa [Nat.sub_add_cancel h1] at this
  have hp1 : ∀ z, z ≤ 7 + 6 * k → parent (X k) 1 z =
      findLastIdx (fun m => decide (ent m 1 < ent (col (X k) z) 1)) ((X k).take z) :=
    fun z hz => parent1_of_inc (X k) z (by omega) (fun x h1 h2 => hinc x h1 (by omega))
  -- the row-1 ancestors of `C` have row-2 entry ≥ 1, except column 0
  let Q : Nat → Prop := fun a => a ≤ 7 + 6 * k ∧ (a = 0 ∨ 1 ≤ ent (col (X k) a) 2)
  have hQ : ∀ z p, Q z → parent (X k) 1 z = some p → Q p := by
    rintro z p ⟨hzL, _⟩ hp
    have hpz := parent_lt (X k) 1 z p hp
    refine ⟨by omega, ?_⟩
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      apply Nat.not_lt.mp
      intro hlt
      have h2 : ent (col (X k) p) 2 = 0 := by omega
      have hnext := (hadj p (by omega)).2 h2 (hpos p (by omega) (by omega))
      rw [hp1 z hzL] at hp
      exact findLastIdx_take_ne (X k) z p p 1 (by omega) hp hnext rfl
  have hsome : ∀ x, 0 < x → x ≤ 7 + 6 * k → (parent (X k) 1 x).isSome := by
    intro x h1 h2
    rw [hp1 x h2]
    apply findLastIdx_take_isSome (X k) x _ h1 (by omega)
    rw [hcol0]
    have := tail_row1 k _ (col_mem_tail (X k) x h1 (by omega))
    show decide (ent [0, 0, 0, 0] 1 < ent (col (X k) x) 1) = true
    rw [show ent [0, 0, 0, 0] 1 = 0 from rfl]
    simp only [decide_eq_true_eq]
    omega
  have hmem : 0 ∈ (anc (X k) 1 (7 + 6 * k)).tail := by
    have := zero_mem_anc (X k) 1 (7 + 6 * k) hsome
    rw [anc_eq] at this ⊢
    simp only [List.mem_cons] at this
    rcases this with h | h
    · omega
    · exact h
  have hp2 : parent (X k) 2 (7 + 6 * k) = some 0 := by
    rw [parent_succ]
    apply find?_eq_some_zero _ _ _ _ hmem
    · intro a ha ha0
      have hQa := anc_invariant (X k) 1 Q hQ (7 + 6 * k) ⟨Nat.le_refl _, Or.inr (by rw [hlast]; simp [C, ent])⟩
        a (List.mem_of_mem_tail ha)
      rcases hQa.2 with h | h
      · exact absurd h ha0
      · show decide (ent (col (X k) a) 2 < ent (col (X k) (7 + 6 * k)) 2) = false
        rw [hlast, show ent (C k) 2 = 1 from rfl]
        simp only [decide_eq_false_iff_not, Nat.not_lt]
        exact h
    · rw [hlast, hcol0]; simp [C, ent]
  have hp3 : parent (X k) 3 (7 + 6 * k) = some 0 :=
    parent_succ_of_zero (X k) 2 (7 + 6 * k) hp2 (by rw [hlast, hcol0]; simp [C, ent])
  unfold ubim
  rw [hlen, show 8 + 6 * k - 1 = 7 + 6 * k by omega]
  exact hp3

theorem flags (k : Nat) (x y : Nat) (hx : x < P.length) :
    BM2.ascend ((P ++ blk k).drop 0) x y = ascBM2 P x y := by
  show ascBM2 (P ++ blk k) x y = ascBM2 P x y
  exact ascBM2_append P (blk k) x y hx

theorem first_copy (k : Nat) :
    bumpMat (BM2.ascend ((P ++ blk k).drop 0)) (delta 3 (C k) (col (P ++ blk k) 0)) 1 0 P =
      D k ++ [C (k + 1)] := by
  rw [bumpMat_congr _ (ascBM2 P) _ _ 0 P (fun x' _ h2 => funext fun y => flags k x' y (by simpa using h2))]
  have hc : col (P ++ blk k) 0 = [0, 0, 0, 0] := rfl
  rw [hc]
  have hf : ∀ x, x < 7 → ∀ y, y < 3 → ascBM2 [[0,0,0,0],[1,1,1,1],[2,2,1,1],[3,3,1,1],[4,2,0,0],[5,1,1,1],[6,2,1,1]] x y =
      ([[true,true,true],[true,true,true],[true,true,true],[true,true,true],[true,true,false],
        [true,true,false],[true,true,false]].getD x []).getD y false := by decide
  simp [P, D, C, bumpMat, bumpCol, delta, ent, hf] <;> omega

theorem loop : Loop BM2 S 1 := by
  constructor
  · rintro _ ⟨k, rfl⟩
    simp [X]
  · rintro _ ⟨k, rfl⟩ n hn
    obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM2) (A := P ++ blk k) (C := C k) (t := 3) (r := 0)
      n hn rfl (badRoot k) (by simp [P]) P (blk k) rfl _ (first_copy k)
    refine ⟨X (k + 1), Z, ⟨k + 1, rfl⟩, ?_⟩
    change expand BM2 ((P ++ blk k) ++ [C k]) n = _
    rw [hZ]
    simp [X, blk]

end DeadBms.BM2.Ex
