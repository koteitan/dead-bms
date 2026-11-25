import «1y-bismuth-2020-07-15».Model

/-!
# Standardness (version of 2020-07-15)

A sequence is standard when the program reaches it from some `(1,m)` by
expansions `(s)[n]` with brackets `n ≥ 0` (the program accepts `(…)[0]`).  The
target `(1,4,12,9,12,20)` is reached from `(1,5)` in 58 expansions, with the
brackets 0 and 1.
-/

namespace Bismuth2020

open Bismuth (R Row)

/-- `s → t`: the program outputs `t` for `(s)[n]` with some bracket `n ≥ 0` -/
def Step (s t : Row) : Prop :=
  ∃ n : Nat, ∃ (f : Nat) (n' : Int), main f s n = .ok (t, n')

/-- `s →* t` -/
inductive Reach : Row → Row → Prop
  | refl (s : Row) : Reach s s
  | step {s t u : Row} : Step s t → Reach t u → Reach s u

/-- reachable from some `(1, m)` -/
def Std (t : Row) : Prop := ∃ m : Int, Reach [1, m] t

/-- the output of `(s)[n]` is `t`, checked with fuel 100 -/
def stepOk (s : Row) (n : Nat) (t : Row) : Bool :=
  match main 100 s n with
  | .ok (u, _) => u == t
  | _ => false

/-- the first sequence of a path, or `t` for the empty path -/
def headOr : List (Row × Nat) → Row → Row
  | [], t => t
  | (s, _) :: _, _ => s

/-- every `(s, n)` of the path expands to the next sequence (the last one to `t`) -/
def chainOk : List (Row × Nat) → Row → Bool
  | [], _ => true
  | (s, n) :: rest, t => stepOk s n (headOr rest t) && chainOk rest t

theorem step_of_stepOk {s : Row} {n : Nat} {t : Row} (h : stepOk s n t = true) : Step s t := by
  unfold stepOk at h
  split at h
  · rename_i u n' hu
    have : u = t := by simpa using h
    subst this
    exact ⟨n, 100, n', hu⟩
  · cases h

theorem reach_of_chainOk : ∀ (p : List (Row × Nat)) (t : Row),
    chainOk p t = true → Reach (headOr p t) t
  | [], t, _ => Reach.refl t
  | (s, n) :: rest, t, h => by
    simp only [chainOk, Bool.and_eq_true] at h
    obtain ⟨hs, hr⟩ := h
    exact Reach.step (step_of_stepOk hs) (reach_of_chainOk rest t hr)

/-- the sequence whose expansion never ends -/
def target : Row := [1, 4, 12, 9, 12, 20]

/-- the path from `(1,5)` to `target`: each sequence with the bracket used -/
def path : List (Row × Nat) :=
  [([1, 5], 1), ([1, 4, 16], 0), ([1, 4, 15], 0), ([1, 4, 14], 0), ([1, 4, 13], 1),
   ([1, 4, 12, 32], 0), ([1, 4, 12, 31], 0), ([1, 4, 12, 30], 0), ([1, 4, 12, 29], 0),
   ([1, 4, 12, 28], 0), ([1, 4, 12, 27], 0), ([1, 4, 12, 26], 1), ([1, 4, 12, 25], 0),
   ([1, 4, 12, 24], 0), ([1, 4, 12, 23], 0), ([1, 4, 12, 22], 0), ([1, 4, 12, 21], 1),
   ([1, 4, 12, 20], 0), ([1, 4, 12, 19], 0), ([1, 4, 12, 18], 0), ([1, 4, 12, 17], 0),
   ([1, 4, 12, 16], 1), ([1, 4, 12, 15, 23], 0), ([1, 4, 12, 15, 22], 0),
   ([1, 4, 12, 15, 21], 0), ([1, 4, 12, 15, 20], 0), ([1, 4, 12, 15, 19], 0),
   ([1, 4, 12, 15], 0), ([1, 4, 12, 14], 0), ([1, 4, 12, 13], 1), ([1, 4, 12, 12], 0),
   ([1, 4, 12, 11], 0), ([1, 4, 12, 10], 1), ([1, 4, 12, 9, 21, 55, 49], 0),
   ([1, 4, 12, 9, 21, 55, 48], 0), ([1, 4, 12, 9, 21, 55, 47], 0),
   ([1, 4, 12, 9, 21, 55, 46], 0), ([1, 4, 12, 9, 21, 55], 0), ([1, 4, 12, 9, 21, 54], 0),
   ([1, 4, 12, 9, 21, 53], 0), ([1, 4, 12, 9, 21, 52], 0), ([1, 4, 12, 9, 21, 51], 0),
   ([1, 4, 12, 9, 21, 50], 0), ([1, 4, 12, 9, 21, 49], 0), ([1, 4, 12, 9, 21, 48], 0),
   ([1, 4, 12, 9, 21, 47], 0), ([1, 4, 12, 9, 21, 46], 0), ([1, 4, 12, 9, 21], 0),
   ([1, 4, 12, 9, 20], 0), ([1, 4, 12, 9, 19], 0), ([1, 4, 12, 9, 18], 0),
   ([1, 4, 12, 9, 17], 1), ([1, 4, 12, 9, 16], 0), ([1, 4, 12, 9, 15], 1),
   ([1, 4, 12, 9, 14], 0), ([1, 4, 12, 9, 13], 1), ([1, 4, 12, 9, 12, 20, 17], 0),
   ([1, 4, 12, 9, 12, 20, 16], 0)]

theorem path_ok : chainOk path target = true := by decide +kernel

/-- `target` is standard -/
theorem std_target : Std target := ⟨5, reach_of_chainOk path target path_ok⟩

end Bismuth2020
