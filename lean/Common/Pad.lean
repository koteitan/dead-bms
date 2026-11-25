import Common.Rules
import Common.Lemmas

/-!
# Zero rows at the bottom do not matter

For a matrix `M` whose columns all have `L` rows,

  `expand R (padM N M) n = padM N (expand R M n)`,

so `M` and `padM N M` (zero rows appended) halt or loop together.  The rules
read entries only through `ent`, and `ent (padCol N c) y = ent c y`.
-/

namespace DeadBms

/-! ## entries -/

theorem ent_append_replicate_zero (c : Col) (m y : Nat) :
    ent (c ++ List.replicate m 0) y = ent c y := by
  unfold ent
  by_cases h : y < c.length
  · simp [List.getElem?_append_left h]
  · have h' : c.length ≤ y := Nat.le_of_not_lt h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h',
      List.getElem?_replicate, List.getElem?_eq_none h']
    split <;> rfl

@[simp] theorem ent_padCol (N : Nat) (c : Col) (y : Nat) : ent (padCol N c) y = ent c y :=
  ent_append_replicate_zero c _ y

@[simp] theorem ent_col_map_padCol (N : Nat) (M : Mat) (x y : Nat) :
    ent (col (M.map (padCol N)) x) y = ent (col M x) y := by
  unfold col
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases M[x]? with
  | none => rfl
  | some c => exact ent_padCol N c y

theorem lowestNZ_replicate_zero : ∀ m, lowestNZ (List.replicate m 0) = none
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, lowestNZ, lowestNZ_replicate_zero m]

@[simp] theorem lowestNZ_padCol (N : Nat) (c : Col) : lowestNZ (padCol N c) = lowestNZ c := by
  unfold padCol
  generalize N - c.length = m
  induction c with
  | nil => simp [lowestNZ_replicate_zero, lowestNZ]
  | cons a c ih => simp [lowestNZ, ih]

theorem lowestNZ_lt : ∀ (c : Col) {t : Nat}, lowestNZ c = some t → t < c.length
  | [], _, h => by simp [lowestNZ] at h
  | a :: c, t, h => by
    simp only [lowestNZ] at h
    cases hc : lowestNZ c with
    | none =>
      rw [hc] at h
      by_cases ha : a = 0
      · simp [ha] at h
      · simp [ha] at h; subst h; simp
    | some s =>
      rw [hc] at h
      simp at h
      have := lowestNZ_lt c hc
      simp; omega

theorem findLastIdx_map {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ l : List α, findLastIdx p (l.map f) = findLastIdx (fun a => p (f a)) l
  | [] => rfl
  | a :: l => by simp [findLastIdx, findLastIdx_map p f l]

/-! ## the rules do not see the zero rows -/

theorem leftAdj_padM (N : Nat) (M : Mat) (t : Nat) : leftAdj (padM N M) t = leftAdj M t := by
  unfold leftAdj padM
  rw [← List.map_dropLast, findLastIdx_map]
  simp

theorem parent0_padM (N : Nat) (M : Mat) (x : Nat) : parent0 (padM N M) x = parent0 M x := by
  unfold parent0 padM
  rw [← List.map_take, findLastIdx_map]
  simp

theorem parent_padM (N : Nat) (M : Mat) : ∀ y x, parent (padM N M) y x = parent M y x
  | 0, x => parent0_padM N M x
  | y + 1, x => by
    have ih : parent (padM N M) y = parent M y := funext (parent_padM N M y)
    simp only [parent, ih]
    unfold padM
    simp

theorem ubim_padM (N : Nat) (M : Mat) (t : Nat) : ubim (padM N M) t = ubim M t := by
  unfold ubim
  rw [parent_padM]
  simp [padM]

theorem ascBM2Aux_padM (N : Nat) (B : Mat) (y : Nat) :
    ∀ fuel x, ascBM2Aux (padM N B) y fuel x = ascBM2Aux B y fuel x
  | _, 0 => by simp [ascBM2Aux]
  | 0, _ + 1 => by simp [ascBM2Aux]
  | fuel + 1, x + 1 => by
    simp only [ascBM2Aux, pLeft, parent0_padM]
    cases parent0 B (x + 1) with
    | none => rfl
    | some k =>
      simp only [ascBM2Aux_padM N B y fuel k]
      unfold padM
      simp

theorem ascBM3Aux_padM (N : Nat) (B : Mat) (y : Nat) :
    ∀ fuel x, ascBM3Aux (padM N B) y fuel x = ascBM3Aux B y fuel x
  | _, 0 => by simp [ascBM3Aux]
  | 0, _ + 1 => by simp [ascBM3Aux]
  | fuel + 1, x + 1 => by
    simp only [ascBM3Aux, pLeft, parent0_padM]
    cases parent0 B (x + 1) with
    | none => rfl
    | some k =>
      simp only [ascBM3Aux_padM N B y fuel k]
      unfold padM
      simp

/-- a rule set whose rules do not see zero rows at the bottom -/
structure RuleSet.PadInv (R : RuleSet) : Prop where
  badRoot : ∀ N M t, R.badRoot (padM N M) t = R.badRoot M t
  ascend : ∀ N B, R.ascend (padM N B) = R.ascend B

theorem padInv_of (b : Mat → Nat → Option Nat) (a : Mat → Nat → Nat → Bool) (f : Nat → Nat)
    (hb : ∀ N M t, b (padM N M) t = b M t) (ha : ∀ N B, a (padM N B) = a B) :
    RuleSet.PadInv { badRoot := b, ascend := a, f := f } := ⟨hb, ha⟩

theorem leftAdj_padInv : ∀ N M t, leftAdj (padM N M) t = leftAdj M t := leftAdj_padM
theorem ubim_padInv : ∀ N M t, ubim (padM N M) t = ubim M t := ubim_padM
theorem ascAll_padInv : ∀ N B, ascAll (padM N B) = ascAll B := fun _ _ => rfl
theorem ascBM2_padInv : ∀ N B, ascBM2 (padM N B) = ascBM2 B := by
  intro N B; funext x y; exact ascBM2Aux_padM N B y x x
theorem ascBM3_padInv : ∀ N B, ascBM3 (padM N B) = ascBM3 B := by
  intro N B; funext x y; simp [ascBM3, ascBM3Aux_padM]

theorem BM1_padInv : BM1.PadInv := padInv_of _ _ _ leftAdj_padInv ascAll_padInv
theorem rTSS_padInv : rTSS.PadInv := padInv_of _ _ _ leftAdj_padInv ascAll_padInv
theorem BM1_1_padInv : BM1_1.PadInv := padInv_of _ _ _ ubim_padInv ascAll_padInv
theorem BM2_1_padInv : BM2_1.PadInv := padInv_of _ _ _ ubim_padInv ascAll_padInv
theorem Bubby3fix_padInv : Bubby3fix.PadInv := padInv_of _ _ _ ubim_padInv ascAll_padInv
theorem BM2_padInv : BM2.PadInv := padInv_of _ _ _ ubim_padInv ascBM2_padInv
theorem BM3_padInv : BM3.PadInv := padInv_of _ _ _ ubim_padInv ascBM3_padInv

/-! ## Δ and the copies -/

theorem ent_zero_eq_headD (r : Col) : ent r 0 = r.headD 0 := by cases r <;> rfl
theorem ent_succ_eq_tail (r : Col) (y : Nat) : ent r (y + 1) = ent r.tail y := by
  cases r <;> simp [ent]

theorem ent_delta : ∀ (t : Nat) (c r : Col) (y : Nat),
    ent (delta t c r) y = if y < c.length ∧ y < t then ent c y - ent r y else 0
  | 0, c, r, y => by
    simp only [delta, Nat.not_lt_zero, and_false, if_false]
    unfold ent
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases c[y]? <;> rfl
  | _ + 1, [], _, y => by simp [delta]
  | t + 1, a :: c, r, 0 => by simp [delta, ent_zero_eq_headD]
  | t + 1, a :: c, r, y + 1 => by
    simp only [delta]
    rw [ent_cons_succ, ent_delta t c r.tail y, ent_cons_succ, ent_succ_eq_tail r y, List.length_cons]
    by_cases h : y < c.length ∧ y < t
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem length_bumpCol (a : Nat → Bool) (Δ : Col) (k : Nat) :
    ∀ (y : Nat) (b : Col), (bumpCol a Δ k y b).length = b.length
  | _, [] => rfl
  | y, _ :: b => by simp [bumpCol, length_bumpCol a Δ k (y + 1) b]

theorem bumpCol_append (a : Nat → Bool) (Δ : Col) (k : Nat) :
    ∀ (y : Nat) (u v : Col), bumpCol a Δ k y (u ++ v) = bumpCol a Δ k y u ++ bumpCol a Δ k (y + u.length) v
  | y, [], v => by simp [bumpCol]
  | y, w :: u, v => by
    simp only [List.cons_append, bumpCol, List.length_cons, bumpCol_append a Δ k (y + 1) u v]
    simp only [Nat.add_assoc, Nat.add_comm 1 u.length]

theorem bumpCol_replicate_zero (a : Nat → Bool) (Δ : Col) (k : Nat) :
    ∀ (m y : Nat), (∀ i, y ≤ i → ent Δ i = 0) → bumpCol a Δ k y (List.replicate m 0) = List.replicate m 0
  | 0, _, _ => rfl
  | m + 1, y, h => by
    simp only [List.replicate_succ, bumpCol, h y (Nat.le_refl y), Nat.mul_zero, Nat.zero_add, ite_self]
    rw [bumpCol_replicate_zero a Δ k m (y + 1) (fun i hi => h i (by omega))]

theorem bumpCol_congr (a : Nat → Bool) (Δ Δ' : Col) (k : Nat) (h : ∀ i, ent Δ i = ent Δ' i) :
    ∀ (y : Nat) (b : Col), bumpCol a Δ k y b = bumpCol a Δ' k y b
  | _, [] => rfl
  | y, v :: b => by simp [bumpCol, h y, bumpCol_congr a Δ Δ' k h (y + 1) b]

theorem bumpCol_padCol (a : Nat → Bool) (Δ Δ' : Col) (k N : Nat) (b : Col)
    (h : ∀ i, ent Δ' i = ent Δ i) (hz : ∀ i, b.length ≤ i → ent Δ i = 0) :
    bumpCol a Δ' k 0 (padCol N b) = padCol N (bumpCol a Δ k 0 b) := by
  unfold padCol
  rw [bumpCol_congr a Δ' Δ k h, bumpCol_append, length_bumpCol,
    bumpCol_replicate_zero a Δ k _ _ (fun i hi => hz i (by omega))]

theorem bumpMat_padM (A : Nat → Nat → Bool) (Δ Δ' : Col) (k N L : Nat)
    (h : ∀ i, ent Δ' i = ent Δ i) (hz : ∀ i, L ≤ i → ent Δ i = 0) :
    ∀ (x : Nat) (B : Mat), (∀ b ∈ B, b.length = L) →
      bumpMat A Δ' k x (padM N B) = padM N (bumpMat A Δ k x B)
  | _, [], _ => rfl
  | x, b :: B, hB => by
    have hb : b.length = L := hB b (by simp)
    have ih := bumpMat_padM A Δ Δ' k N L h hz (x + 1) B (fun c hc => hB c (by simp [hc]))
    simp only [padM, List.map_cons, bumpMat] at ih ⊢
    rw [ih, bumpCol_padCol (A x) Δ Δ' k N b h (fun i hi => hz i (by omega))]

theorem copies_padM (A : Nat → Nat → Bool) (Δ Δ' : Col) (N L : Nat) (B : Mat)
    (h : ∀ i, ent Δ' i = ent Δ i) (hz : ∀ i, L ≤ i → ent Δ i = 0) (hB : ∀ b ∈ B, b.length = L) :
    ∀ n, copies (padM N B) A Δ' n = padM N (copies B A Δ n)
  | 0 => rfl
  | n + 1 => by
    rw [copies, copies, copies_padM A Δ Δ' N L B h hz hB n,
      bumpMat_padM A Δ Δ' (n + 1) N L h hz 0 B hB]
    simp [padM]

/-! ## uniform matrices -/

/-- every column has `L` rows -/
def Uniform (L : Nat) (M : Mat) : Prop := ∀ c ∈ M, c.length = L

instance (L : Nat) (M : Mat) : Decidable (Uniform L M) := by
  unfold Uniform; infer_instance

theorem length_bumpMat_mem (A : Nat → Nat → Bool) (Δ : Col) (k L : Nat) :
    ∀ (x : Nat) (B : Mat), Uniform L B → Uniform L (bumpMat A Δ k x B)
  | _, [], _ => by simp [bumpMat, Uniform]
  | x, b :: B, hB => by
    intro c hc
    simp only [bumpMat, List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [length_bumpCol]; exact hB b (by simp)
    · exact length_bumpMat_mem A Δ k L (x + 1) B (fun c hc => hB c (by simp [hc])) c hc

theorem uniform_copies (A : Nat → Nat → Bool) (Δ : Col) (L : Nat) (B : Mat) (hB : Uniform L B) :
    ∀ n, Uniform L (copies B A Δ n)
  | 0 => by simp [copies, Uniform]
  | n + 1 => by
    intro c hc
    simp only [copies, List.mem_append] at hc
    rcases hc with hc | hc
    · exact uniform_copies A Δ L B hB n c hc
    · exact length_bumpMat_mem A Δ (n + 1) L 0 B hB c hc

theorem uniform_of_sublist {L : Nat} {M M' : Mat} (h : M' ⊆ M) (hM : Uniform L M) : Uniform L M' :=
  fun c hc => hM c (h hc)

theorem uniform_expand (R : RuleSet) {L : Nat} {M : Mat} (hM : Uniform L M) (n : Nat) :
    Uniform L (expand R M n) := by
  have hd : Uniform L M.dropLast := uniform_of_sublist (List.dropLast_subset M) hM
  unfold expand
  split
  · simp [Uniform]
  · split
    · exact hd
    · split
      · exact hd
      · intro c hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hd c hc
        · exact uniform_copies _ _ L _ (uniform_of_sublist (List.drop_subset _ _) hd) n c hc

/-! ## expansion commutes with padding -/

theorem expand_padM {R : RuleSet} (hR : R.PadInv) {L : Nat} (N : Nat) {M : Mat}
    (hM : Uniform L M) (n : Nat) : expand R (padM N M) n = padM N (expand R M n) := by
  have hlast : (padM N M).getLast? = M.getLast?.map (padCol N) := by simp [padM]
  have hdrop : (padM N M).dropLast = padM N M.dropLast := by simp [padM, List.map_dropLast]
  unfold expand
  rw [hlast]
  cases hC : M.getLast? with
  | none => rfl
  | some C =>
    simp only [Option.map_some, lowestNZ_padCol]
    cases ht : lowestNZ C with
    | none => exact hdrop
    | some t =>
      simp only
      rw [hR.badRoot]
      cases hr : R.badRoot M t with
      | none => exact hdrop
      | some r =>
        simp only
        have hCmem : C ∈ M := List.mem_of_getLast? hC
        have hCL : C.length = L := hM C hCmem
        have htC : t < C.length := lowestNZ_lt C ht
        have hB : Uniform L (M.dropLast.drop r) :=
          uniform_of_sublist ((List.drop_subset _ _).trans (List.dropLast_subset M)) hM
        have hd2 : (padM N M).dropLast.drop r = padM N (M.dropLast.drop r) := by
          rw [hdrop]; simp [padM, List.map_drop]
        have hΔ : ∀ i, ent (delta t (padCol N C) (col (padM N M) r)) i = ent (delta t C (col M r)) i := by
          intro i
          rw [ent_delta, ent_delta]
          simp only [ent_padCol, padM, ent_col_map_padCol]
          by_cases hi : i < t
          · rw [if_pos ⟨by simp [padCol]; omega, hi⟩, if_pos ⟨by omega, hi⟩]
          · rw [if_neg (fun h => hi h.2), if_neg (fun h => hi h.2)]
        have hz : ∀ i, L ≤ i → ent (delta t C (col M r)) i = 0 := by
          intro i hi
          rw [ent_delta, if_neg (by omega)]
        rw [hd2, hR.ascend, copies_padM _ _ _ N L _ hΔ hz hB, hdrop]
        simp [padM]

theorem compute_padM {R : RuleSet} (hR : R.PadInv) {L : Nat} (N : Nat) :
    ∀ (i : Nat) (M : Mat) (n : Nat), Uniform L M →
      compute R (padM N M) n i = (padM N (compute R M n i).1, (compute R M n i).2)
  | 0, _, _, _ => rfl
  | i + 1, M, n, hM => by
    simp only [compute]
    rw [expand_padM hR N hM]
    exact compute_padM hR N i _ _ (uniform_expand R hM _)

theorem halts_padM {R : RuleSet} (hR : R.PadInv) {L : Nat} (N : Nat) {M : Mat}
    (hM : Uniform L M) (n : Nat) : Halts R (padM N M) n ↔ Halts R M n := by
  unfold Halts
  constructor
  · rintro ⟨i, hi⟩
    rw [compute_padM hR N i M n hM] at hi
    exact ⟨i, by simpa [padM] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [compute_padM hR N i M n hM]; simp [padM, hi]⟩

end DeadBms
