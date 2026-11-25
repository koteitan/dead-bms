import Common.Ubim
import Common.Rules

/-!
# BM1.1: the loop

With `T_j = (j,j,0)(j+1,j+1,1)(j+2,0,0)`, `Q_k = T_0 ⁀ T_1 ⁀ ⋯ ⁀ T_k` and
`E_k = (k+1,k+1,0)(k+2,k+2,1)`, one period consists of six matrices
(rows and columns are 0-indexed):

| phase | matrix                                   | t | bad root      | next      |
|-------|------------------------------------------|---|---------------|-----------|
| s0 k  | Q_k (k+1,k+1,1)                          | 2 | `(k,k,0)` of `T_k` | s1 k |
| s1 k  | Q_k E_k (k+3,1,0)                        | 1 | column 0      | s2 k      |
| s2 k  | Q_k E_k (k+3,0,0) (k+4,1,1)              | 2 | `(k+3,0,0)`   | s3 k      |
| s3 k  | Q_k E_k (k+3,0,0) (k+4,1,0)              | 1 | `(k+3,0,0)`   | s4 k      |
| s4 k  | Q_k E_k (k+3,0,0) (k+4,0,0)              | 0 | `(k+3,0,0)`   | s5 k      |
| s5 k  | Q_k E_k (k+3,0,0) (k+3,0,0)              | 0 | `(k+2,k+2,1)` | s0 (k+1)  |

and `Q_{k+1} = Q_k E_k (k+3,0,0)`.  In each phase the next matrix is a prefix
of the expansion with any bracket `n ≥ 1` (it is `M⁻` followed by the first
columns of `B_1`).

For s1, the row-0 parent of a column is the rightmost column left of it with
a smaller row-0 entry.  Every column `(j+2,0,0)` (row-1 entry 0) is followed
by `(j+1,j+1,0)`, which is smaller in row 0, so it is never such a parent;
hence the row-0 ancestors of `(k+3,1,0)` other than column 0 have row-1
entries `≥ 1`, and the row-1 parent is column 0.
-/

namespace DeadBms.BM1_1.Ex

def T (j : Nat) : Mat := [[j, j, 0], [j + 1, j + 1, 1], [j + 2, 0, 0]]

/-- `T_1 ⁀ ⋯ ⁀ T_k` -/
def qr : Nat → Mat
  | 0 => []
  | k + 1 => qr k ++ T (k + 1)

/-- `Q_k = T_0 ⁀ T_1 ⁀ ⋯ ⁀ T_k` -/
def q (k : Nat) : Mat := T 0 ++ qr k

def E (k : Nat) : Mat := [[k + 1, k + 1, 0], [k + 2, k + 2, 1]]

/-- `Q_k E_k (k+3,0,0) = Q_{k+1}` -/
def F (k : Nat) : Mat := (q k ++ E k) ++ [[k + 3, 0, 0]]

def s0 (k : Nat) : Mat := q k ++ [[k + 1, k + 1, 1]]
def s1 (k : Nat) : Mat := (q k ++ E k) ++ [[k + 3, 1, 0]]
def s2 (k : Nat) : Mat := F k ++ [[k + 4, 1, 1]]
def s3 (k : Nat) : Mat := F k ++ [[k + 4, 1, 0]]
def s4 (k : Nat) : Mat := F k ++ [[k + 4, 0, 0]]
def s5 (k : Nat) : Mat := F k ++ [[k + 3, 0, 0]]

def S (W : Mat) : Prop :=
  ∃ k, W = s0 k ∨ W = s1 k ∨ W = s2 k ∨ W = s3 k ∨ W = s4 k ∨ W = s5 k

theorem len_qr : ∀ k, (qr k).length = 3 * k
  | 0 => rfl
  | k + 1 => by simp [qr, len_qr k, T]; omega

theorem len_q (k : Nat) : (q k).length = 3 * k + 3 := by
  simp [q, len_qr, T] <;> omega

theorem q_succ (k : Nat) : q (k + 1) = F k := by
  simp [q, qr, F, T, E]

/-- the last block of `Q_k` is `T_k` -/
theorem q_last : ∀ k, ∃ pre : Mat, q k = pre ++ T k ∧ pre.length = 3 * k
  | 0 => ⟨[], rfl, rfl⟩
  | k + 1 => ⟨q k, by simp [q, qr], by have := len_q k; omega⟩

theorem q_getLast : ∀ k, (q k).getLast? = some [k + 2, 0, 0]
  | 0 => rfl
  | k + 1 => by
    rw [q_succ, F]
    simp

/-! ### phase 0 -/

theorem root0 (k : Nat) : ubim (s0 k) 2 = some (3 * k) := by
  obtain ⟨pre, hq, hpre⟩ := q_last k
  have hcol : col (s0 k) (3 * k) = [k, k, 0] := by
    rw [s0, col_append_left _ _ (by rw [len_q]; omega), hq, ← hpre]
    simp [T, col]
  have hp0 : parent (s0 k) 0 (q k).length = some (3 * k) := by
    show parent0 (q k ++ [[k + 1, k + 1, 1]]) (q k).length = _
    rw [parent0_snoc, hq, findLastIdx_append_some _ pre (T k) (i := 0)]
    · rw [hpre]; rfl
    · simp [findLastIdx, T, ent]
  have hp1 := parent_succ_of_first (s0 k) 0 _ _ hp0 (by
    rw [hcol, show col (s0 k) (q k).length = [k + 1, k + 1, 1] from col_snoc _ _]
    simp [ent])
  have hp2 := parent_succ_of_first (s0 k) 1 _ _ hp1 (by
    rw [hcol, show col (s0 k) (q k).length = [k + 1, k + 1, 1] from col_snoc _ _]
    simp [ent])
  rw [s0, ubim_snoc]
  exact hp2

theorem step0 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s0 k) n = s1 k ++ Z := by
  obtain ⟨pre, hq, hpre⟩ := q_last k
  have hdrop : (q k).drop (3 * k) = T k := by rw [hq, ← hpre, List.drop_left]
  have hcol : col (q k) (3 * k) = [k, k, 0] := by
    rw [hq, ← hpre]
    simp [T, col]
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := q k) (C := [k + 1, k + 1, 1]) (t := 2)
    (r := 3 * k) n hn rfl (root0 k) (by rw [len_q]; omega) (T k) [] (by rw [hdrop]; simp)
    (E k ++ [[k + 3, 1, 0]]) (by
      rw [hcol]
      simp [BM1_1, ascAll, T, E, bumpMat, bumpCol, delta, ent] <;> omega)
  exact ⟨Z, by rw [show s0 k = q k ++ [[k + 1, k + 1, 1]] from rfl, hZ]; simp [s1]⟩

/-! ### phase 1 -/

/-- the relation between adjacent columns used in phase 1 -/
def R1 (a b : Col) : Prop := ent a 1 = 0 → ent b 0 ≤ ent a 0

theorem qr_getLast (k : Nat) : ((T 0).tail ++ qr k).getLast? = some [k + 2, 0, 0] := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [qr, ← List.append_assoc, List.getLast?_append]
    simp [T]

theorem adj_qr : ∀ k, Adj R1 ((T 0).tail ++ qr k)
  | 0 => by simp [Adj, R1, T, qr, ent]
  | k + 1 => by
    rw [qr, ← List.append_assoc]
    refine adj_append R1 _ _ (adj_qr k) ?_ ?_
    · simp [Adj, R1, T, ent]
    · intro a b ha hb
      rw [qr_getLast] at ha
      simp [T] at hb
      cases ha; cases hb
      simp [R1, ent]

theorem s1_tail (k : Nat) : (s1 k).tail = (((T 0).tail ++ qr k) ++ E k) ++ [[k + 3, 1, 0]] := by
  simp [s1, q, T]

theorem adj_s1 (k : Nat) : Adj R1 (s1 k).tail := by
  rw [s1_tail]
  refine adj_append R1 _ _ (adj_append R1 _ _ (adj_qr k) ?_ ?_) trivial ?_
  · simp [Adj, R1, E, ent]
  · intro a b ha hb
    rw [qr_getLast] at ha
    simp [E] at hb
    cases ha; cases hb
    simp [R1, ent]
  · intro a b ha hb
    simp [E] at ha
    simp at hb
    cases ha; cases hb
    simp [R1, ent]

theorem qr_row0 : ∀ k, ∀ c ∈ qr k, 0 < ent c 0
  | 0, _, h => by simp [qr] at h
  | k + 1, c, h => by
    simp only [qr, List.mem_append] at h
    rcases h with h | h
    · exact qr_row0 k c h
    · simp [T] at h
      rcases h with rfl | rfl | rfl <;> simp [ent]

theorem s1_row0 (k : Nat) : ∀ c ∈ (s1 k).tail, 0 < ent c 0 := by
  intro c hc
  rw [s1_tail] at hc
  simp only [List.mem_append, T, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, E] at hc
  rcases hc with (((rfl | rfl) | h) | (rfl | rfl)) | rfl
  all_goals first | exact qr_row0 k c h | simp [ent]

theorem root1 (k : Nat) : ubim (s1 k) 1 = some 0 := by
  have hlen : (s1 k).length = 3 * k + 6 := by
    rw [s1, List.length_append, List.length_append, len_q] <;> simp [E] <;> omega
  have hlast : col (s1 k) (3 * k + 5) = [k + 3, 1, 0] := by
    have := col_snoc (q k ++ E k) [k + 3, 1, 0]
    rwa [List.length_append, len_q, show (E k).length = 2 from rfl,
      show 3 * k + 3 + 2 = 3 * k + 5 by omega] at this
  have hcol0 : col (s1 k) 0 = [0, 0, 0] := rfl
  have hadj := adj_tail_col R1 (s1 k) (adj_s1 k)
  have hpos : ∀ x, 0 < x → x < (s1 k).length → 0 < ent (col (s1 k) x) 0 :=
    fun x h1 h2 => s1_row0 k _ (col_mem_tail (s1 k) x h1 h2)
  -- the row-0 ancestors of the last column, other than column 0, have row-1 entry ≥ 1
  let Q : Nat → Prop := fun a => a ≤ 3 * k + 5 ∧ (a = 0 ∨ 1 ≤ ent (col (s1 k) a) 1)
  have hQ : ∀ z p, Q z → parent (s1 k) 0 z = some p → Q p := by
    rintro z p ⟨hzL, _⟩ hp
    have hpz := parent_lt (s1 k) 0 z p hp
    refine ⟨by omega, ?_⟩
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      apply Nat.not_lt.mp
      intro hlt
      have h1 : ent (col (s1 k) p) 1 = 0 := by omega
      have hnext := hadj p (by omega) (by omega) h1
      exact findLastIdx_take_ne (s1 k) z p p 0 (by omega) hp hnext rfl
  have hsome : ∀ x, 0 < x → x ≤ 3 * k + 5 → (parent (s1 k) 0 x).isSome := by
    intro x h1 h2
    apply parent0_isSome (s1 k) x h1 (by omega)
    rw [hcol0]
    exact hpos x h1 (by omega)
  have hmem : 0 ∈ (anc (s1 k) 0 (3 * k + 5)).tail := by
    have := zero_mem_anc (s1 k) 0 (3 * k + 5) hsome
    rw [anc_eq] at this ⊢
    simp only [List.mem_cons] at this
    rcases this with h | h
    · omega
    · exact h
  have hp1 : parent (s1 k) 1 (3 * k + 5) = some 0 := by
    rw [parent_succ]
    apply find?_eq_some_zero _ _ _ _ hmem
    · intro a ha ha0
      have hQa := anc_invariant (s1 k) 0 Q hQ (3 * k + 5)
        ⟨Nat.le_refl _, Or.inr (by rw [hlast]; simp [ent])⟩ a (List.mem_of_mem_tail ha)
      rcases hQa.2 with h | h
      · exact absurd h ha0
      · show decide (ent (col (s1 k) a) 1 < ent (col (s1 k) (3 * k + 5)) 1) = false
        rw [hlast, show ent [k + 3, 1, 0] 1 = 1 from rfl]
        simp only [decide_eq_false_iff_not, Nat.not_lt]
        exact h
    · rw [hlast, hcol0]; simp [ent]
  unfold ubim
  rw [hlen, show 3 * k + 6 - 1 = 3 * k + 5 by omega]
  exact hp1

theorem step1 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s1 k) n = s2 k ++ Z := by
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := q k ++ E k) (C := [k + 3, 1, 0]) (t := 1)
    (r := 0) n hn rfl (root1 k) (by simp [q, T]) [[0, 0, 0], [1, 1, 1]] ([[2, 0, 0]] ++ qr k ++ E k)
    (by simp [q, T]) [[k + 3, 0, 0], [k + 4, 1, 1]] (by
      show bumpMat (fun _ _ => true) (delta 1 [k + 3, 1, 0] [0, 0, 0]) 1 0 [[0, 0, 0], [1, 1, 1]] = _
      simp [bumpMat, bumpCol, delta, ent] <;> omega)
  exact ⟨Z, by rw [show s1 k = (q k ++ E k) ++ [[k + 3, 1, 0]] from rfl, hZ]; simp [s2, F]⟩

/-! ### phases 2–5 -/

theorem len_qE (k : Nat) : (q k ++ E k).length = 3 * k + 5 := by
  simp [len_q, E] <;> omega

theorem parentF (k : Nat) (C : Col) (hC : k + 3 < ent C 0) :
    parent (F k ++ [C]) 0 (F k).length = some (q k ++ E k).length := by
  show parent0 (F k ++ [C]) (F k).length = _
  rw [parent0_snoc, F, findLastIdx_snoc]
  have : decide (ent [k + 3, 0, 0] 0 < ent C 0) = true := decide_eq_true (by rw [ent_cons_zero]; exact hC)
  rw [if_pos this]

theorem colF (k : Nat) (C : Col) : col (F k ++ [C]) (q k ++ E k).length = [k + 3, 0, 0] := by
  rw [F, col_append_left _ _ (by simp), col_snoc]

theorem dropF (k : Nat) : (F k).drop (q k ++ E k).length = [[k + 3, 0, 0]] := by
  rw [F, List.drop_left]

theorem step2 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s2 k) n = s3 k ++ Z := by
  have hp0 := parentF k [k + 4, 1, 1] (by simp [ent])
  have hc := colF k [k + 4, 1, 1]
  have hL : col (F k ++ [[k + 4, 1, 1]]) (F k).length = [k + 4, 1, 1] := col_snoc _ _
  have hp1 := parent_succ_of_first _ 0 _ _ hp0 (by rw [hc, hL]; simp [ent])
  have hp2 := parent_succ_of_first _ 1 _ _ hp1 (by rw [hc, hL]; simp [ent])
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := F k) (C := [k + 4, 1, 1]) (t := 2)
    (r := (q k ++ E k).length) n hn rfl (by show ubim (F k ++ [[k + 4, 1, 1]]) 2 = _; rw [ubim_snoc]; exact hp2) (by simp [F])
    [[k + 3, 0, 0]] [] (by rw [dropF]; simp) [[k + 4, 1, 0]] (by
      rw [show col (F k) (q k ++ E k).length = [k + 3, 0, 0] by rw [F]; exact col_snoc _ _]
      simp [BM1_1, ascAll, bumpMat, bumpCol, delta, ent] <;> omega)
  exact ⟨Z, by rw [show s2 k = F k ++ [[k + 4, 1, 1]] from rfl, hZ]; simp [s3]⟩

theorem step3 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s3 k) n = s4 k ++ Z := by
  have hp0 := parentF k [k + 4, 1, 0] (by simp [ent])
  have hc := colF k [k + 4, 1, 0]
  have hL : col (F k ++ [[k + 4, 1, 0]]) (F k).length = [k + 4, 1, 0] := col_snoc _ _
  have hp1 := parent_succ_of_first _ 0 _ _ hp0 (by rw [hc, hL]; simp [ent])
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := F k) (C := [k + 4, 1, 0]) (t := 1)
    (r := (q k ++ E k).length) n hn rfl (by show ubim (F k ++ [[k + 4, 1, 0]]) 1 = _; rw [ubim_snoc]; exact hp1) (by simp [F])
    [[k + 3, 0, 0]] [] (by rw [dropF]; simp) [[k + 4, 0, 0]] (by
      rw [show col (F k) (q k ++ E k).length = [k + 3, 0, 0] by rw [F]; exact col_snoc _ _]
      simp [BM1_1, ascAll, bumpMat, bumpCol, delta, ent] <;> omega)
  exact ⟨Z, by rw [show s3 k = F k ++ [[k + 4, 1, 0]] from rfl, hZ]; simp [s4]⟩

theorem step4 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s4 k) n = s5 k ++ Z := by
  have hp0 := parentF k [k + 4, 0, 0] (by simp [ent])
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := F k) (C := [k + 4, 0, 0]) (t := 0)
    (r := (q k ++ E k).length) n hn rfl (by show ubim (F k ++ [[k + 4, 0, 0]]) 0 = _; rw [ubim_snoc]; exact hp0) (by simp [F])
    [[k + 3, 0, 0]] [] (by rw [dropF]; simp) [[k + 3, 0, 0]] (by
      simp [BM1_1, ascAll, bumpMat, bumpCol, delta, ent])
  exact ⟨Z, by rw [show s4 k = F k ++ [[k + 4, 0, 0]] from rfl, hZ]; simp [s5]⟩

theorem step5 (k n : Nat) (hn : 0 < n) : ∃ Z, expand BM1_1 (s5 k) n = s0 (k + 1) ++ Z := by
  have hp0 : parent (F k ++ [[k + 3, 0, 0]]) 0 (F k).length = some ((q k).length + 1) := by
    show parent0 (F k ++ [[k + 3, 0, 0]]) (F k).length = _
    rw [parent0_snoc, F, findLastIdx_snoc]
    simp only [ent_cons_zero, Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false]
    rw [findLastIdx_append_some _ (q k) (E k) (i := 1) (by simp [findLastIdx, E, ent])]
  have hdrop : (F k).drop ((q k).length + 1) = [[k + 2, k + 2, 1], [k + 3, 0, 0]] := by
    rw [F, List.append_assoc, List.drop_append]
    simp [E]
  obtain ⟨Z, hZ⟩ := expand_snoc_prefix (R := BM1_1) (A := F k) (C := [k + 3, 0, 0]) (t := 0)
    (r := (q k).length + 1) n hn rfl (by show ubim (F k ++ [[k + 3, 0, 0]]) 0 = _; rw [ubim_snoc]; exact hp0) (by simp [F, E])
    [[k + 2, k + 2, 1]] [[k + 3, 0, 0]] (hdrop.trans rfl) [[k + 2, k + 2, 1]] (by
      simp [BM1_1, ascAll, bumpMat, bumpCol, delta, ent])
  exact ⟨Z, by rw [show s5 k = F k ++ [[k + 3, 0, 0]] from rfl, hZ, s0, q_succ]⟩

theorem loop : Loop BM1_1 S 1 := by
  constructor
  · rintro _ ⟨k, h | h | h | h | h | h⟩ <;> subst h <;> simp [s0, s1, s2, s3, s4, s5]
  · rintro _ ⟨k, h | h | h | h | h | h⟩ n hn <;> subst h
    · obtain ⟨Z, hZ⟩ := step0 k n hn
      exact ⟨_, Z, ⟨k, Or.inr (Or.inl rfl)⟩, hZ⟩
    · obtain ⟨Z, hZ⟩ := step1 k n hn
      exact ⟨_, Z, ⟨k, Or.inr (Or.inr (Or.inl rfl))⟩, hZ⟩
    · obtain ⟨Z, hZ⟩ := step2 k n hn
      exact ⟨_, Z, ⟨k, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, hZ⟩
    · obtain ⟨Z, hZ⟩ := step3 k n hn
      exact ⟨_, Z, ⟨k, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, hZ⟩
    · obtain ⟨Z, hZ⟩ := step4 k n hn
      exact ⟨_, Z, ⟨k, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩, hZ⟩
    · obtain ⟨Z, hZ⟩ := step5 k n hn
      exact ⟨_, Z, ⟨k + 1, Or.inl rfl⟩, hZ⟩

end DeadBms.BM1_1.Ex
