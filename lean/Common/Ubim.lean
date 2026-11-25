import Common.Lemmas

/-!
# Lemmas on the Upper-Branch-Ignoring Model

`anc M y x` is the list of ancestors of the element at column `x`, row `y`
(`x` itself first, then its parent, …).  The parent in row `y + 1` is the
first element of `(anc M y x).tail` whose row-`(y+1)` entry is smaller.
-/

namespace DeadBms

theorem getD_eq_getElem' {α : Type} (l : List α) (d : α) (n : Nat) (h : n < l.length) :
    l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## specification of `findLastIdx` -/

theorem findLastIdx_eq_none_iff {α : Type} (p : α → Bool) :
    ∀ l : List α, findLastIdx p l = none ↔ ∀ a ∈ l, p a = false
  | [] => by simp [findLastIdx]
  | a :: l => by
    simp only [findLastIdx]
    cases h : findLastIdx p l with
    | none =>
      have hl := (findLastIdx_eq_none_iff p l).1 h
      by_cases ha : p a = true
      · simp only [ha, if_true]
        constructor
        · intro h'; cases h'
        · intro hall; have := hall a (by simp); simp [ha] at this
      · have ha' : p a = false := by simpa using ha
        simp only [ha', Bool.false_eq_true, if_false, true_iff]
        intro b hb
        simp at hb
        rcases hb with rfl | hb
        · exact ha'
        · exact hl b hb
    | some i =>
      simp only [reduceCtorEq, false_iff]
      intro hall
      have : findLastIdx p l = none := (findLastIdx_eq_none_iff p l).2 (fun b hb => hall b (by simp [hb]))
      rw [this] at h
      cases h

theorem findLastIdx_some {α : Type} (p : α → Bool) (d : α) :
    ∀ (l : List α) (i : Nat), findLastIdx p l = some i →
      i < l.length ∧ p (l.getD i d) = true ∧ ∀ j, i < j → j < l.length → p (l.getD j d) = false
  | [], i, h => by simp [findLastIdx] at h
  | a :: l, i, h => by
    simp only [findLastIdx] at h
    cases hl : findLastIdx p l with
    | none =>
      rw [hl] at h
      have hall := (findLastIdx_eq_none_iff p l).1 hl
      by_cases ha : p a = true
      · simp only [ha, if_true, Option.some.injEq] at h
        subst h
        refine ⟨by simp, by simpa using ha, ?_⟩
        intro j hj hjl
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [List.length_cons] at hjl
        simp only [List.getD_cons_succ]
        rw [getD_eq_getElem' _ _ _ (by omega)]
        exact hall _ (List.getElem_mem _)
      · simp [ha] at h
    | some i' =>
      rw [hl] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := findLastIdx_some p d l i' hl
      refine ⟨by simp; omega, by simpa using h2, ?_⟩
      intro j hj hjl
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ]
      exact h3 j' (by omega) (by simp at hjl; omega)

theorem findLastIdx_of {α : Type} (p : α → Bool) (d : α) (l : List α) (i : Nat)
    (h1 : i < l.length) (h2 : p (l.getD i d) = true)
    (h3 : ∀ j, i < j → j < l.length → p (l.getD j d) = false) : findLastIdx p l = some i := by
  cases h : findLastIdx p l with
  | none =>
    have := (findLastIdx_eq_none_iff p l).1 h (l.getD i d)
      (by rw [getD_eq_getElem' _ _ _ h1]; exact List.getElem_mem _)
    rw [this] at h2
    cases h2
  | some i' =>
    obtain ⟨h1', h2', h3'⟩ := findLastIdx_some p d l i' h
    congr 1
    rcases Nat.lt_trichotomy i' i with hlt | heq | hgt
    · have := h3' i hlt h1; rw [this] at h2; cases h2
    · exact heq
    · have := h3 i' hgt h1'; rw [this] at h2'; cases h2'

/-! ## columns of `take` -/

theorem getD_take_col (M : Mat) (x j : Nat) (h : j < x) : (M.take x).getD j [] = col M j := by
  unfold col
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

/-! ## parents are to the left -/

theorem parent0_lt (M : Mat) (x p : Nat) (h : parent0 M x = some p) : p < x := by
  have := findLastIdx_lt _ _ h
  simp at this
  omega

theorem chain_mem_le (par : Nat → Option Nat) (hpar : ∀ z p, par z = some p → p < z) :
    ∀ (fuel x a : Nat), a ∈ chain par fuel x → a ≤ x
  | 0, x, a, h => by simp [chain] at h; omega
  | fuel + 1, x, a, h => by
    simp only [chain, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · cases hp : par x with
      | none => rw [hp] at h; simp at h
      | some p =>
        rw [hp] at h
        have := chain_mem_le par hpar fuel p a h
        have := hpar x p hp
        omega

theorem chain_tail_lt (par : Nat → Option Nat) (hpar : ∀ z p, par z = some p → p < z)
    (fuel x a : Nat) (h : a ∈ (chain par fuel x).tail) : a < x := by
  cases fuel with
  | zero => simp [chain] at h
  | succ fuel =>
    simp only [chain, List.tail_cons] at h
    cases hp : par x with
    | none => rw [hp] at h; simp at h
    | some p =>
      rw [hp] at h
      have := chain_mem_le par hpar fuel p a h
      have := hpar x p hp
      omega

theorem parent_lt (M : Mat) : ∀ (y x p : Nat), parent M y x = some p → p < x
  | 0, x, p, h => parent0_lt M x p h
  | y + 1, x, p, h => by
    simp only [parent] at h
    have hmem := List.mem_of_find?_eq_some h
    exact chain_tail_lt (parent M y) (parent_lt M y) x x p hmem

theorem parent_zero_none (M : Mat) (y : Nat) : parent M y 0 = none := by
  cases h : parent M y 0 with
  | none => rfl
  | some p => have := parent_lt M y 0 p h; omega

/-! ## ancestors -/

theorem chain_eq (par : Nat → Option Nat) (hpar : ∀ z p, par z = some p → p < z) :
    ∀ (f g x : Nat), x ≤ f → x ≤ g → chain par f x = chain par g x
  | 0, 0, x, _, _ => rfl
  | 0, g + 1, x, hf, _ => by
    have hx : x = 0 := by omega
    subst hx
    have : par 0 = none := by
      cases h : par 0 with
      | none => rfl
      | some p => have := hpar 0 p h; omega
    simp [chain, this]
  | f + 1, 0, x, _, hg => by
    have hx : x = 0 := by omega
    subst hx
    have : par 0 = none := by
      cases h : par 0 with
      | none => rfl
      | some p => have := hpar 0 p h; omega
    simp [chain, this]
  | f + 1, g + 1, x, hf, hg => by
    simp only [chain]
    cases hp : par x with
    | none => rfl
    | some p =>
      have := hpar x p hp
      simp only
      rw [chain_eq par hpar f g p (by omega) (by omega)]

/-- the ancestors of the element at column `x`, row `y` (`x` first) -/
def anc (M : Mat) (y x : Nat) : List Nat := chain (parent M y) x x

theorem anc_eq (M : Mat) (y x : Nat) :
    anc M y x = x :: match parent M y x with
      | none => []
      | some p => anc M y p := by
  unfold anc
  cases x with
  | zero => simp [chain, parent_zero_none]
  | succ x =>
    simp only [chain]
    cases hp : parent M y (x + 1) with
    | none => rfl
    | some p =>
      have := parent_lt M y (x + 1) p hp
      simp only
      rw [chain_eq (parent M y) (parent_lt M y) x p p (by omega) (by omega)]

theorem anc_of_parent (M : Mat) (y x p : Nat) (h : parent M y x = some p) :
    anc M y x = x :: anc M y p := by
  rw [anc_eq, h]

theorem anc_of_parent_none (M : Mat) (y x : Nat) (h : parent M y x = none) : anc M y x = [x] := by
  rw [anc_eq, h]

theorem anc_zero (M : Mat) (y : Nat) : anc M y 0 = [0] :=
  anc_of_parent_none M y 0 (parent_zero_none M y)

theorem parent_succ (M : Mat) (y x : Nat) :
    parent M (y + 1) x = (anc M y x).tail.find? fun a =>
      decide (ent (col M a) (y + 1) < ent (col M x) (y + 1)) := rfl

theorem mem_anc_tail_lt (M : Mat) (y x a : Nat) (h : a ∈ (anc M y x).tail) : a < x :=
  chain_tail_lt (parent M y) (parent_lt M y) x x a h

/-- the chain of ancestors reaches column 0 when every column on the way has a parent -/
theorem zero_mem_anc (M : Mat) (y : Nat) :
    ∀ x, (∀ x', 0 < x' → x' ≤ x → (parent M y x').isSome) → 0 ∈ anc M y x := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro h
    cases x with
    | zero => simp [anc_zero]
    | succ x =>
      have hs := h (x + 1) (by omega) (Nat.le_refl _)
      cases hp : parent M y (x + 1) with
      | none => rw [hp] at hs; cases hs
      | some p =>
        have hpx := parent_lt M y (x + 1) p hp
        rw [anc_of_parent M y (x + 1) p hp]
        exact List.mem_cons_of_mem _ (ih p hpx (fun x' h1 h2 => h x' h1 (by omega)))

/-- every ancestor satisfies an invariant that parents preserve -/
theorem anc_invariant (M : Mat) (y : Nat) (Q : Nat → Prop)
    (hQ : ∀ z p, Q z → parent M y z = some p → Q p) :
    ∀ x, Q x → ∀ a ∈ anc M y x, Q a := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx a ha
    cases hp : parent M y x with
    | none =>
      rw [anc_of_parent_none M y x hp] at ha
      simp at ha
      rw [ha]; exact hx
    | some p =>
      rw [anc_of_parent M y x p hp] at ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hx
      · exact ih p (parent_lt M y x p hp) (hQ x p hx hp) a ha

theorem find?_eq_some_zero (l : List Nat) (q : Nat → Bool)
    (hskip : ∀ a ∈ l, a ≠ 0 → q a = false) (h0 : q 0 = true) (hmem : 0 ∈ l) :
    l.find? q = some 0 := by
  induction l with
  | nil => simp at hmem
  | cons a l ih =>
    by_cases ha : a = 0
    · subst ha; simp [h0]
    · have hqa : q a = false := hskip a (by simp) ha
      simp only [List.find?_cons, hqa]
      apply ih
      · intro b hb; exact hskip b (by simp [hb])
      · simp at hmem
        rcases hmem with h | h
        · exact absurd h.symm ha
        · exact h

/-- once the parent is column 0, it stays column 0 in the rows below (when column
0 is smaller there) -/
theorem parent_succ_of_zero (M : Mat) (y x : Nat) (h : parent M y x = some 0)
    (hlt : ent (col M 0) (y + 1) < ent (col M x) (y + 1)) : parent M (y + 1) x = some 0 := by
  rw [parent_succ, anc_of_parent M y x 0 h, anc_zero]
  simp [hlt]

/-- parent in row 0, when every earlier column is smaller -/
theorem parent0_isSome (M : Mat) (x : Nat) (hx : 0 < x) (hxl : x ≤ M.length)
    (h : ent (col M 0) 0 < ent (col M x) 0) : (parent0 M x).isSome := by
  unfold parent0
  cases hf : findLastIdx (fun m => decide (ent m 0 < ent (col M x) 0)) (M.take x) with
  | some _ => rfl
  | none =>
    have hall := (findLastIdx_eq_none_iff _ _).1 hf
    have hlen : 0 < (M.take x).length := by simp; omega
    have := hall ((M.take x).getD 0 []) (by rw [getD_eq_getElem' _ _ _ hlen]; exact List.getElem_mem _)
    rw [getD_take_col M x 0 hx] at this
    simp [h] at this

/-- `col M x` is in `M.tail` for `0 < x < M.length` -/
theorem col_mem_tail (M : Mat) (x : Nat) (hx : 0 < x) (hxl : x < M.length) : col M x ∈ M.tail := by
  cases M with
  | nil => simp at hxl
  | cons c M =>
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    simp only [List.length_cons] at hxl
    simp only [col, List.getD_cons_succ, List.tail_cons]
    rw [getD_eq_getElem' _ _ _ (by omega)]
    exact List.getElem_mem _


/-! ## adjacent columns -/

/-- `R` holds for every pair of adjacent columns -/
def Adj (R : Col → Col → Prop) : Mat → Prop
  | [] => True
  | [_] => True
  | a :: b :: M => R a b ∧ Adj R (b :: M)

theorem adj_append (R : Col → Col → Prop) : ∀ (A B : Mat), Adj R A → Adj R B →
    (∀ a b, A.getLast? = some a → B.head? = some b → R a b) → Adj R (A ++ B)
  | [], B, _, hB, _ => by simpa using hB
  | [_], [], _, _, _ => trivial
  | [a], b :: B, _, hB, h => ⟨h a b rfl rfl, hB⟩
  | a :: a' :: A, B, hA, hB, h => by
    obtain ⟨h1, hA⟩ := hA
    exact ⟨h1, adj_append R (a' :: A) B hA hB (fun x y hx hy => h x y (by simpa using hx) hy)⟩

theorem adj_col (R : Col → Col → Prop) :
    ∀ (M : Mat), Adj R M → ∀ i, i + 1 < M.length → R (col M i) (col M (i + 1))
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: M, hM, 0, _ => by simpa [col] using hM.1
  | a :: b :: M, hM, i + 1, h => by
    have := adj_col R (b :: M) hM.2 i (by simp at h ⊢; omega)
    simpa [col] using this

/-! ## the rightmost smaller column -/

theorem findLastIdx_snoc {α : Type} (p : α → Bool) (l : List α) (a : α) :
    findLastIdx p (l ++ [a]) = if p a then some l.length else findLastIdx p l := by
  by_cases ha : p a = true
  · rw [if_pos ha, findLastIdx_append_some p l [a] (i := 0) (by simp [findLastIdx, ha])]
    rfl
  · rw [if_neg ha, findLastIdx_append_none p l [a] (by simp [findLastIdx, ha])]

/-- the rightmost column left of `z` with a smaller row-`y` entry is never a
column `a` whose right neighbour is not larger in row `y` -/
theorem findLastIdx_take_ne (M : Mat) (z p a y : Nat) (hz : z < M.length)
    (h : findLastIdx (fun m => decide (ent m y < ent (col M z) y)) (M.take z) = some p)
    (hnext : ent (col M (a + 1)) y ≤ ent (col M a) y) : p ≠ a := by
  intro hpa
  subst hpa
  obtain ⟨h1, h2, h3⟩ := findLastIdx_some _ [] _ _ h
  simp only [List.length_take] at h1
  have hpz : p < z := by omega
  rw [getD_take_col M z p hpz] at h2
  simp only [decide_eq_true_eq] at h2
  by_cases hz' : p + 1 = z
  · subst hz'
    omega
  · have := h3 (p + 1) (by omega) (by simp only [List.length_take]; omega)
    rw [getD_take_col M z (p + 1) (by omega)] at this
    simp only [decide_eq_false_iff_not, Nat.not_lt] at this
    omega

theorem findLastIdx_take_isSome (M : Mat) (x : Nat) (q : Col → Bool) (hx : 0 < x)
    (hxl : x ≤ M.length) (h : q (col M 0) = true) : (findLastIdx q (M.take x)).isSome := by
  cases hf : findLastIdx q (M.take x) with
  | some _ => rfl
  | none =>
    have hall := (findLastIdx_eq_none_iff _ _).1 hf
    have hlen : 0 < (M.take x).length := by simp; omega
    have := hall ((M.take x).getD 0 []) (by rw [getD_eq_getElem' _ _ _ hlen]; exact List.getElem_mem _)
    rw [getD_take_col M x 0 hx, h] at this
    cases this

theorem parent0_of_prev (M : Mat) (x : Nat) (hx : 0 < x) (hxl : x ≤ M.length)
    (h : ent (col M (x - 1)) 0 < ent (col M x) 0) : parent0 M x = some (x - 1) := by
  unfold parent0
  apply findLastIdx_of _ [] _ _ (by simp; omega)
  · rw [getD_take_col M x (x - 1) (by omega)]; simpa using h
  · intro j h1 h2; simp at h2; omega

theorem find?_range_reverse (M : Mat) (q : Col → Bool) :
    ∀ z, z ≤ M.length → (List.range z).reverse.find? (fun a => q (col M a)) = findLastIdx q (M.take z)
  | 0, _ => by simp [findLastIdx]
  | z + 1, hz => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons, find?_range_reverse M q z (by omega)]
    have htake : M.take (z + 1) = M.take z ++ [col M z] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp [col, List.getElem?_eq_getElem (show z < M.length by omega)]
    rw [htake, findLastIdx_snoc]
    have hl : (M.take z).length = z := by simp; omega
    rw [hl]
    cases q (col M z) <;> rfl

/-- if row 0 strictly increases up to `z`, the ancestors in row 0 are all the
columns `z, z-1, …, 0` -/
theorem anc_of_inc (M : Mat) :
    ∀ z, (∀ x, 0 < x → x ≤ z → parent M 0 x = some (x - 1)) → anc M 0 z = (List.range (z + 1)).reverse
  | 0, _ => by simp [anc_zero]
  | z + 1, h => by
    rw [anc_of_parent M 0 (z + 1) z (by simpa using h (z + 1) (by omega) (Nat.le_refl _)),
      anc_of_inc M z (fun x h1 h2 => h x h1 (by omega)), List.range_succ (n := z + 1)]
    simp

/-- if row 0 strictly increases up to `z`, the parent in row 1 is the rightmost
column left of `z` with a smaller row-1 entry -/
theorem parent1_of_inc (M : Mat) (z : Nat) (hz : z ≤ M.length)
    (h : ∀ x, 0 < x → x ≤ z → parent M 0 x = some (x - 1)) :
    parent M 1 z = findLastIdx (fun m => decide (ent m 1 < ent (col M z) 1)) (M.take z) := by
  rw [parent_succ, anc_of_inc M z h, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.tail_cons]
  exact find?_range_reverse M (fun m => decide (ent m 1 < ent (col M z) 1)) z hz


/-! ## matrices of the form `A ⁀ C` -/

theorem parent0_snoc (A : Mat) (C : Col) :
    parent0 (A ++ [C]) A.length = findLastIdx (fun m => decide (ent m 0 < ent C 0)) A := by
  unfold parent0
  rw [List.take_left' rfl, col_snoc]

theorem ubim_snoc (A : Mat) (C : Col) (t : Nat) : ubim (A ++ [C]) t = parent (A ++ [C]) t A.length := by
  unfold ubim
  simp

/-- if the parent in row `y` is already smaller in row `y + 1`, it is also the
parent in row `y + 1` -/
theorem parent_succ_of_first (M : Mat) (y x p : Nat) (h : parent M y x = some p)
    (hlt : ent (col M p) (y + 1) < ent (col M x) (y + 1)) : parent M (y + 1) x = some p := by
  rw [parent_succ, anc_of_parent M y x p h, anc_eq]
  simp [hlt]

theorem adj_tail_col (R : Col → Col → Prop) (M : Mat) (h : Adj R M.tail) (i : Nat) (hi : 1 ≤ i)
    (hil : i + 1 < M.length) : R (col M i) (col M (i + 1)) := by
  cases M with
  | nil => simp at hil
  | cons c M =>
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have := adj_col R M h i' (by simp at hil; omega)
    simpa [col] using this

/-! ## ascension flags read only the columns up to `x` -/

theorem parent0_append (A W : Mat) (x : Nat) (hx : x < A.length) :
    parent0 (A ++ W) x = parent0 A x := by
  unfold parent0
  rw [List.take_append_of_le_length (Nat.le_of_lt hx), col_append_left A W hx]

theorem ascBM2Aux_append (A W : Mat) (y : Nat) (hA : 0 < A.length) :
    ∀ fuel x, x < A.length → ascBM2Aux (A ++ W) y fuel x = ascBM2Aux A y fuel x
  | _, 0, _ => by simp [ascBM2Aux]
  | 0, _ + 1, _ => by simp [ascBM2Aux]
  | fuel + 1, x + 1, hx => by
    simp only [ascBM2Aux, pLeft, parent0_append A W (x + 1) hx]
    cases hp : parent0 A (x + 1) with
    | none => rfl
    | some k =>
      have hk := parent0_lt A (x + 1) k hp
      simp only
      rw [ascBM2Aux_append A W y hA fuel k (by omega), col_append_left A W hA,
        col_append_left A W hx]

theorem ascBM2_append (A W : Mat) (x y : Nat) (hx : x < A.length) :
    ascBM2 (A ++ W) x y = ascBM2 A x y :=
  ascBM2Aux_append A W y (by omega) x x hx

theorem ascBM3Aux_append (A W : Mat) (y : Nat) :
    ∀ fuel x, x < A.length → ascBM3Aux (A ++ W) y fuel x = ascBM3Aux A y fuel x
  | _, 0, _ => by simp [ascBM3Aux]
  | 0, _ + 1, _ => by simp [ascBM3Aux]
  | fuel + 1, x + 1, hx => by
    simp only [ascBM3Aux, pLeft, parent0_append A W (x + 1) hx]
    cases hp : parent0 A (x + 1) with
    | none => rfl
    | some k =>
      have hk := parent0_lt A (x + 1) k hp
      simp only
      rw [ascBM3Aux_append A W y fuel k (by omega), col_append_left A W (by omega),
        col_append_left A W hx]

theorem ascBM3_append (A W : Mat) (x y : Nat) (hx : x < A.length) :
    ascBM3 (A ++ W) x y = ascBM3 A x y := by
  unfold ascBM3
  rw [ascBM3Aux_append A W y x x hx]

/-- The bad root is column 0 when column 0 is zero, every other column is
positive in row 0, the middle columns are at least `c_1` in row 1, and `c_y > 0`
for `1 ≤ y ≤ t`. -/
theorem ubim_eq_zero (M : Mat) (t : Nat) (ht : 1 ≤ t) (hlen : 2 ≤ M.length)
    (h0 : ∀ y, ent (col M 0) y = 0)
    (hrow0 : ∀ c ∈ M.tail, 0 < ent c 0)
    (hrow1 : ∀ c ∈ M.tail.dropLast, ent (col M (M.length - 1)) 1 ≤ ent c 1)
    (hc : ∀ y, 1 ≤ y → y ≤ t → 0 < ent (col M (M.length - 1)) y) :
    ubim M t = some 0 := by
  unfold ubim
  generalize hL : M.length - 1 = L
  have hL0 : 0 < L := by omega
  have hLl : L < M.length := by omega
  -- row 0: the chain of ancestors reaches column 0
  have hsome : ∀ x', 0 < x' → x' ≤ L → (parent M 0 x').isSome := by
    intro x' h1 h2
    exact parent0_isSome M x' h1 (by omega)
      (by rw [h0]; exact hrow0 _ (col_mem_tail M x' h1 (by omega)))
  have hmem0 : 0 ∈ (anc M 0 L).tail := by
    have := zero_mem_anc M 0 L hsome
    rw [anc_eq] at this
    simp only [List.mem_cons] at this
    rcases this with h | h
    · omega
    · rw [anc_eq]; exact h
  -- row 1: column 0 is the parent
  have hp1 : parent M 1 L = some 0 := by
    rw [parent_succ]
    apply find?_eq_some_zero _ _ _ _ hmem0
    · intro a ha ha0
      have haL := mem_anc_tail_lt M 0 L a ha
      have hmid : col M a ∈ M.tail.dropLast := by
        cases M with
        | nil => simp at hlen
        | cons c M =>
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          simp only [List.length_cons] at hL
          simp only [col, List.getD_cons_succ, List.tail_cons]
          rw [getD_eq_getElem' _ _ _ (by omega)]
          rw [← List.getElem_dropLast (by simp; omega)]
          exact List.getElem_mem _
      have := hrow1 _ hmid
      rw [hL] at this
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      exact this
    · simp only [decide_eq_true_eq, h0]
      have := hc 1 (Nat.le_refl 1) ht
      rw [hL] at this
      exact this
  -- rows 2..t
  have : ∀ y, 1 ≤ y → y ≤ t → parent M y L = some 0 := by
    intro y hy1 hyt
    induction y with
    | zero => omega
    | succ y ih =>
      cases y with
      | zero => exact hp1
      | succ y =>
        apply parent_succ_of_zero M (y + 1) L (ih (by omega) (by omega))
        rw [h0]
        have := hc (y + 2) (by omega) hyt
        rw [hL] at this
        exact this
  exact this t ht (Nat.le_refl t)

end DeadBms
