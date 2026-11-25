import Common.Loop

/-!
# Lemmas for computing expansions of families of matrices
-/

namespace DeadBms

/-! ## `findLastIdx` -/

theorem findLastIdx_append_some {α : Type} (p : α → Bool) (l₁ l₂ : List α) {i : Nat}
    (h : findLastIdx p l₂ = some i) : findLastIdx p (l₁ ++ l₂) = some (l₁.length + i) := by
  induction l₁ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append, findLastIdx, ih, List.length_cons]
    congr 1
    omega

theorem findLastIdx_append_none {α : Type} (p : α → Bool) (l₁ l₂ : List α)
    (h : findLastIdx p l₂ = none) : findLastIdx p (l₁ ++ l₂) = findLastIdx p l₁ := by
  induction l₁ with
  | nil => simp [h, findLastIdx]
  | cons a l ih => simp only [List.cons_append, findLastIdx, ih]

theorem findLastIdx_eq_none {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ a ∈ l, p a = false) : findLastIdx p l = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : p a = false := h a (by simp)
    have hl : findLastIdx p l = none := ih (fun b hb => h b (by simp [hb]))
    simp [findLastIdx, hl, ha]

theorem findLastIdx_lt {α : Type} (p : α → Bool) :
    ∀ (l : List α) {i : Nat}, findLastIdx p l = some i → i < l.length
  | [], _, h => by simp [findLastIdx] at h
  | a :: l, i, h => by
    simp only [findLastIdx] at h
    cases hl : findLastIdx p l with
    | none =>
      rw [hl] at h
      by_cases ha : p a = true
      · simp [ha] at h; subst h; simp
      · simp [ha] at h
    | some j =>
      rw [hl] at h
      simp at h
      have := findLastIdx_lt p l hl
      simp; omega

/-! ## columns and entries -/

@[simp] theorem ent_nil (y : Nat) : ent [] y = 0 := by simp [ent]
@[simp] theorem ent_cons_zero (a : Nat) (c : Col) : ent (a :: c) 0 = a := by simp [ent]
@[simp] theorem ent_cons_succ (a : Nat) (c : Col) (y : Nat) : ent (a :: c) (y + 1) = ent c y := by
  simp [ent]

theorem col_append_left (A B : Mat) {x : Nat} (h : x < A.length) : col (A ++ B) x = col A x := by
  simp [col, List.getElem?_append_left h]

theorem col_append_right (A B : Mat) (x : Nat) : col (A ++ B) (A.length + x) = col B x := by
  simp [col, List.getElem?_append_right]

theorem col_snoc (A : Mat) (C : Col) : col (A ++ [C]) A.length = C := by
  simp [col]

theorem col_last (A : Mat) (C : Col) : col (A ++ [C]) ((A ++ [C]).length - 1) = C := by
  have h : (A ++ [C]).length - 1 = A.length := by simp
  rw [h, col_snoc]

/-! ## the shape of an expansion -/

theorem expand_snoc {R : RuleSet} {A : Mat} {C : Col} {t r : Nat} (n : Nat)
    (ht : lowestNZ C = some t) (hr : R.badRoot (A ++ [C]) t = some r) (hrA : r < A.length) :
    expand R (A ++ [C]) n =
      A ++ copies (A.drop r) (R.ascend (A.drop r)) (delta t C (col A r)) n := by
  have hcol : col (A ++ [C]) r = col A r := col_append_left A [C] hrA
  simp [expand, ht, hr, hcol]

theorem copies_pos (B : Mat) (A : Nat → Nat → Bool) (Δ : Col) :
    ∀ n, 0 < n → ∃ W, copies B A Δ n = bumpMat A Δ 1 0 B ++ W
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => ⟨[], by simp [copies]⟩
  | n + 2, _ => by
    obtain ⟨W, hW⟩ := copies_pos B A Δ (n + 1) (Nat.succ_pos n)
    exact ⟨W ++ bumpMat A Δ (n + 2) 0 B, by rw [copies, hW, List.append_assoc]⟩

theorem bumpMat_append (A : Nat → Nat → Bool) (Δ : Col) (k : Nat) :
    ∀ (U V : Mat) (x : Nat),
      bumpMat A Δ k x (U ++ V) = bumpMat A Δ k x U ++ bumpMat A Δ k (x + U.length) V
  | [], V, x => by simp [bumpMat]
  | u :: U, V, x => by
    simp only [List.cons_append, bumpMat, List.length_cons]
    rw [bumpMat_append A Δ k U V (x + 1)]
    simp only [Nat.add_assoc, Nat.add_comm 1 U.length]

/-- `bumpMat` reads the flags only at the columns it bumps -/
theorem bumpMat_congr (A A' : Nat → Nat → Bool) (Δ : Col) (k : Nat) :
    ∀ (x : Nat) (B : Mat), (∀ x', x ≤ x' → x' < x + B.length → A x' = A' x') →
      bumpMat A Δ k x B = bumpMat A' Δ k x B
  | _, [], _ => rfl
  | x, b :: B, h => by
    simp only [bumpMat]
    rw [h x (Nat.le_refl x) (by simp), bumpMat_congr A A' Δ k (x + 1) B
      (fun x' h1 h2 => h x' (by omega) (by simp; omega))]

/-- if the first columns of the first copy `B_1` are `D`, then `M⁻ ⁀ D` is a
prefix of the expansion -/
theorem expand_snoc_prefix {R : RuleSet} {A : Mat} {C : Col} {t r : Nat} (n : Nat) (hn : 0 < n)
    (ht : lowestNZ C = some t) (hr : R.badRoot (A ++ [C]) t = some r) (hrA : r < A.length)
    (U V : Mat) (hUV : A.drop r = U ++ V) (D : Mat)
    (hD : bumpMat (R.ascend (A.drop r)) (delta t C (col A r)) 1 0 U = D) :
    ∃ Z, expand R (A ++ [C]) n = (A ++ D) ++ Z := by
  rw [expand_snoc n ht hr hrA]
  obtain ⟨W, hW⟩ := copies_pos (A.drop r) (R.ascend (A.drop r)) (delta t C (col A r)) n hn
  refine ⟨bumpMat (R.ascend (A.drop r)) (delta t C (col A r)) 1 (0 + U.length) V ++ W, ?_⟩
  rw [hW]
  conv => lhs; rw [hUV]
  rw [bumpMat_append, ← hUV, hD]
  simp only [List.append_assoc]

/-! ## 左隣法 -/

theorem leftAdj_snoc (A : Mat) (C : Col) (t : Nat) :
    leftAdj (A ++ [C]) t =
      findLastIdx (fun m => (List.range (t + 1)).all fun y => decide (ent m y < ent C y)) A := by
  have h : (A ++ [C]).length - 1 = A.length := by simp
  simp only [leftAdj, h, col_snoc]
  simp

end DeadBms
