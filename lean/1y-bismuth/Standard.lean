import «1y-bismuth».Model

/-!
# Standardness

A sequence is standard when the program reaches it from some `(1,m)` by
expansions with brackets `≥ 1`.  The target `(1,2,4,7,5,4,5,10)` is reached
from `(1,3)` in 19 expansions.
-/

namespace Bismuth

/-- `s → t`: the program outputs `t` for `(s)[b]` with some bracket `b ≥ 1` -/
def Step (s t : Row) : Prop :=
  ∃ b : Nat, 1 ≤ b ∧ ∃ (f : Nat) (b' : Int), main f s b = .ok (t, b')

/-- `s →* t` -/
inductive Reach : Row → Row → Prop
  | refl (s : Row) : Reach s s
  | step {s t u : Row} : Step s t → Reach t u → Reach s u

/-- reachable from some `(1, m)` -/
def Std (t : Row) : Prop := ∃ m : Int, Reach [1, m] t

/-- the output of `(s)[b]` is `t`, checked with fuel 100 -/
def stepOk (s : Row) (b : Nat) (t : Row) : Bool :=
  match main 100 s b with
  | .ok (u, _) => u == t
  | _ => false

/-- the first sequence of a path, or `t` for the empty path -/
def headOr : List (Row × Nat) → Row → Row
  | [], t => t
  | (s, _) :: _, _ => s

/-- every `(s, b)` of the path expands to the next sequence (the last one to `t`) -/
def chainOk : List (Row × Nat) → Row → Bool
  | [], _ => true
  | (s, b) :: rest, t => decide (1 ≤ b) && stepOk s b (headOr rest t) && chainOk rest t

theorem step_of_stepOk {s : Row} {b : Nat} {t : Row} (hb : 1 ≤ b) (h : stepOk s b t = true) :
    Step s t := by
  unfold stepOk at h
  split at h
  · rename_i u b' hu
    have : u = t := by simpa using h
    subst this
    exact ⟨b, hb, 100, b', hu⟩
  · cases h

theorem reach_of_chainOk : ∀ (p : List (Row × Nat)) (t : Row),
    chainOk p t = true → Reach (headOr p t) t
  | [], t, _ => Reach.refl t
  | (s, b) :: rest, t, h => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, hs⟩, hr⟩ := h
    exact Reach.step (step_of_stepOk hb hs) (reach_of_chainOk rest t hr)

/-- the sequence whose expansion never ends -/
def target : Row := [1, 2, 4, 7, 5, 4, 5, 10]

/-- the path from `(1,3)` to `target`: each sequence with the bracket used -/
def path : List (Row × Nat) :=
  [([1, 3], 2), ([1, 2, 4, 8], 3), ([1, 2, 4, 7, 11], 2), ([1, 2, 4, 7, 10], 2),
   ([1, 2, 4, 7, 9, 12], 1), ([1, 2, 4, 7, 9], 2), ([1, 2, 4, 7, 8, 10, 13], 1),
   ([1, 2, 4, 7, 8, 10], 1), ([1, 2, 4, 7, 8], 2), ([1, 2, 4, 7, 7], 2),
   ([1, 2, 4, 7, 6, 9], 1), ([1, 2, 4, 7, 6], 2), ([1, 2, 4, 7, 5, 7, 10], 1),
   ([1, 2, 4, 7, 5, 7], 2), ([1, 2, 4, 7, 5, 6], 2), ([1, 2, 4, 7, 5, 5], 2),
   ([1, 2, 4, 7, 5, 4, 7, 5], 1), ([1, 2, 4, 7, 5, 4, 7], 2), ([1, 2, 4, 7, 5, 4, 6], 2)]

theorem path_ok : chainOk path target = true := by decide +kernel

/-- `target` is standard -/
theorem std_target : Std target := ⟨3, reach_of_chainOk path target path_ok⟩

end Bismuth
