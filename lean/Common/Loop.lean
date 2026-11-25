import Common.Expand

/-!
# Loops imply non-termination

The general lemma used by every example.  Let `S` be a set of matrices with

* `X ≠ ()` for every `X ∈ S`, and
* for every `X ∈ S` and every `n ≥ n₀` there is `Y ∈ S` that is a prefix of
  `expand R X n`.

Then the computation starting from any `X ∈ S` with a bracket `n ≥ n₀` never
reaches the empty matrix (provided `f` keeps brackets `≥ n₀`), and `X` has an
infinite descending sequence `X →_R X₁ →_R X₂ →_R ⋯`.

The key fact is that an expansion keeps every column except the last one, so
`expand (Y ⁀ Z) n = Y ⁀ Z'` when `Z ≠ ()`: the computation of `Y ⁀ Z` either
reaches `Y` exactly, or keeps `Y` as a proper prefix forever.
-/

namespace DeadBms

/-- every expansion keeps the columns left of the last column -/
theorem expand_eq_dropLast_append (R : RuleSet) (M : Mat) (n : Nat) (h : M ≠ []) :
    ∃ W, expand R M n = M.dropLast ++ W := by
  unfold expand
  split
  · rename_i hC
    simp at hC
    exact absurd hC h
  · split
    · exact ⟨[], by simp⟩
    · split
      · exact ⟨[], by simp⟩
      · exact ⟨_, rfl⟩

/-- the expansion with bracket `0` deletes the last column -/
theorem expand_zero (R : RuleSet) (M : Mat) : expand R M 0 = M.dropLast := by
  unfold expand
  split
  · rename_i hC
    simp at hC
    simp [hC]
  · split
    · rfl
    · split
      · rfl
      · simp [copies]

/-- a nonempty suffix is the only part an expansion changes -/
theorem expand_append (R : RuleSet) (X Z : Mat) (n : Nat) (hZ : Z ≠ []) :
    ∃ Z', expand R (X ++ Z) n = X ++ Z' := by
  obtain ⟨W, hW⟩ := expand_eq_dropLast_append R (X ++ Z) n (by simp [hZ])
  refine ⟨Z.dropLast ++ W, ?_⟩
  rw [hW, List.dropLast_append_of_ne_nil hZ, List.append_assoc]

/-- the bracket sequence shifted by `j` -/
def shift (ns : Nat → Nat) (j : Nat) : Nat → Nat := fun k => ns (k + j)

/-- the run of `Y ⁀ Z` either reaches `Y` exactly or keeps a nonempty suffix -/
theorem run_prefix (R : RuleSet) (Y : Mat) :
    ∀ (i : Nat) (Z : Mat) (ns : Nat → Nat),
      (∃ j, j ≤ i ∧ run R (Y ++ Z) ns i = run R Y (shift ns j) (i - j)) ∨
      (∃ Z', Z' ≠ [] ∧ run R (Y ++ Z) ns i = Y ++ Z') := by
  intro i
  induction i with
  | zero =>
    intro Z ns
    by_cases hZ : Z = []
    · left
      subst hZ
      exact ⟨0, Nat.le_refl 0, by simp [run]⟩
    · right
      exact ⟨Z, hZ, rfl⟩
  | succ i ih =>
    intro Z ns
    by_cases hZ : Z = []
    · left
      subst hZ
      exact ⟨0, Nat.zero_le _, by simp; rfl⟩
    · obtain ⟨Z', hZ'⟩ := expand_append R Y Z (ns 0) hZ
      have hrun : run R (Y ++ Z) ns (i + 1) = run R (Y ++ Z') (fun k => ns (k + 1)) i := by
        simp only [run, hZ']
      rcases ih Z' (fun k => ns (k + 1)) with ⟨j, hj, h2⟩ | ⟨Z'', hZ'', h⟩
      · left
        refine ⟨j + 1, by omega, ?_⟩
        rw [hrun, h2, Nat.add_sub_add_right]
        rfl
      · right
        exact ⟨Z'', hZ'', by rw [hrun]; exact h⟩

/-- the loop condition on a set `S` of matrices -/
structure Loop (R : RuleSet) (S : Mat → Prop) (n0 : Nat) : Prop where
  ne : ∀ X, S X → X ≠ []
  step : ∀ X, S X → ∀ n, n0 ≤ n → ∃ Y Z, S Y ∧ expand R X n = Y ++ Z

/-- with brackets `≥ n₀`, a run from `S` never reaches the empty matrix -/
theorem Loop.run_ne_nil {R : RuleSet} {S : Mat → Prop} {n0 : Nat} (L : Loop R S n0) :
    ∀ (i : Nat) (X : Mat) (ns : Nat → Nat), S X → (∀ k, n0 ≤ ns k) → run R X ns i ≠ [] := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro X ns hX hns
    cases i with
    | zero => exact L.ne X hX
    | succ i =>
      obtain ⟨Y, Z, hY, hYZ⟩ := L.step X hX (ns 0) (hns 0)
      have hrun : run R X ns (i + 1) = run R (Y ++ Z) (fun k => ns (k + 1)) i := by
        simp only [run, hYZ]
      rw [hrun]
      rcases run_prefix R Y i Z (fun k => ns (k + 1)) with ⟨j, hj, h2⟩ | ⟨Z', hZ', h⟩
      · rw [h2]
        exact ih (i - j) (by omega) Y _ hY (fun k => hns _)
      · rw [h]
        simp [hZ']

/-- `iter f m n = f^m(n)` -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | m + 1, n => iter f m (f n)

/-- `compute` is `run` with the brackets `f(n), f(f(n)), …` -/
theorem compute_fst (R : RuleSet) :
    ∀ (i : Nat) (M : Mat) (n : Nat), (compute R M n i).1 = run R M (fun k => iter R.f (k + 1) n) i
  | 0, _, _ => rfl
  | i + 1, M, n => by
    simp only [compute, run]
    rw [compute_fst R i]
    rfl

/-- the computation from `S` with a bracket `n ≥ n₀` does not halt -/
theorem Loop.not_halts {R : RuleSet} {S : Mat → Prop} {n0 : Nat} (L : Loop R S n0)
    (hf : ∀ n, n0 ≤ n → n0 ≤ R.f n) :
    ∀ X, S X → ∀ n, n0 ≤ n → ¬ Halts R X n := by
  intro X hX n hn ⟨i, hi⟩
  rw [compute_fst] at hi
  have hit : ∀ m n, n0 ≤ n → n0 ≤ iter R.f m n := by
    intro m
    induction m with
    | zero => intro n hn; exact hn
    | succ m ih => intro n hn; exact ih (R.f n) (hf n hn)
  exact L.run_ne_nil i X _ hX (fun k => hit (k + 1) n hn) hi

/-- matrices that have a prefix in `S` -/
def PrefixIn (S : Mat → Prop) (W : Mat) : Prop := ∃ Y Z, S Y ∧ W = Y ++ Z

/-- every matrix with a prefix in `S` has an expansion with a prefix in `S` -/
theorem Loop.prefixIn_step {R : RuleSet} {S : Mat → Prop} {n0 : Nat} (L : Loop R S n0) :
    ∀ W, PrefixIn S W → ∃ V, PrefixIn S V ∧ Step R W V := by
  rintro W ⟨Y, Z, hY, rfl⟩
  by_cases hZ : Z = []
  · subst hZ
    obtain ⟨Y', Z', hY', h⟩ := L.step Y hY n0 (Nat.le_refl _)
    exact ⟨expand R (Y ++ []) n0, ⟨Y', Z', hY', by simpa using h⟩, ⟨n0, rfl⟩⟩
  · refine ⟨expand R (Y ++ Z) 0, ⟨Y, Z.dropLast, hY, ?_⟩, ⟨0, rfl⟩⟩
    rw [expand_zero, List.dropLast_append_of_ne_nil hZ]

/-- no matrix of `S` is accessible for the expansion relation -/
theorem Loop.not_acc {R : RuleSet} {S : Mat → Prop} {n0 : Nat} (L : Loop R S n0) :
    ∀ X, S X → ¬ Acc (fun B A => Step R A B) X := by
  have key : ∀ W, Acc (fun B A => Step R A B) W → ¬ PrefixIn S W := by
    intro W hacc
    induction hacc with
    | intro W _ ih =>
      intro hW
      obtain ⟨V, hV, hWV⟩ := L.prefixIn_step W hW
      exact ih V hWV hV
  intro X hX hacc
  exact key X hacc ⟨X, [], hX, by simp⟩

/-- `seq 0 = X`, `seq (i+1) = next (seq i)` -/
def iterSeq (next : Mat → Mat) (X : Mat) : Nat → Mat
  | 0 => X
  | i + 1 => next (iterSeq next X i)

/-- every matrix of `S` has an infinite descending sequence -/
theorem Loop.infinite_descent {R : RuleSet} {S : Mat → Prop} {n0 : Nat} (L : Loop R S n0) :
    ∀ X, S X → ∃ seq : Nat → Mat, seq 0 = X ∧ ∀ i, Step R (seq i) (seq (i + 1)) := by
  intro X hX
  classical
  let next : Mat → Mat := fun W =>
    if h : PrefixIn S W then Classical.choose (L.prefixIn_step W h) else W
  have hnext : ∀ W, PrefixIn S W → PrefixIn S (next W) ∧ Step R W (next W) := by
    intro W h
    simp only [next, dif_pos h]
    exact Classical.choose_spec (L.prefixIn_step W h)
  have hseq : ∀ i, PrefixIn S (iterSeq next X i) := by
    intro i
    induction i with
    | zero => exact ⟨X, [], hX, by simp [iterSeq]⟩
    | succ i ih => exact (hnext _ ih).1
  exact ⟨iterSeq next X, rfl, fun i => (hnext _ (hseq i)).2⟩

/-! ## rule sets with the same expansion -/

theorem runList_congr {R R' : RuleSet} (h : ∀ M n, expand R M n = expand R' M n) :
    ∀ M ns, runList R M ns = runList R' M ns
  | _, [] => rfl
  | M, n :: ns => by simp only [runList, h M n, runList_congr h _ ns]

theorem Std.of_expand_eq {R R' : RuleSet} (h : ∀ M n, expand R M n = expand R' M n) {M : Mat}
    (hM : Std R' M) : Std R M := by
  obtain ⟨N, ns, hns⟩ := hM
  exact ⟨N, ns, by rw [runList_congr h]; exact hns⟩

theorem Loop.of_expand_eq {R R' : RuleSet} (h : ∀ M n, expand R M n = expand R' M n)
    {S : Mat → Prop} {n0 : Nat} (L : Loop R' S n0) : Loop R S n0 :=
  ⟨L.ne, fun X hX n hn => by rw [h]; exact L.step X hX n hn⟩

end DeadBms
