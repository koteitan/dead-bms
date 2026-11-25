import Common.Ascend

/-!
# The common expansion rule (共通ルール)

`expand R M n` is one expansion step of the page:

1. `C` is the last column of `M`.
2. If `C` is all zero, there is no bad root.
3. `t` is the lowest nonzero row of `C`.
4. The bad root `R` is found by the bad root rule.
5. `C` is deleted.
6. (The bracket is changed to `f(n)`; this is done by `compute`, not here.)
7. Without a bad root, the step ends here.
8. The bad part `B` is the bad root and the columns right of it.
9. `δ_{xy} = c_y - r_y` for `y < t`, `0` for `y ≥ t`.
10. `A'` is given by the ascension rule.
11. `A = A'` (改変なし).
12. `B_1, …, B_n` are appended, where `B_k = B + k (A ⊗ Δ)`.

So `expand R M n = M⁻ ⁀ B_1 ⁀ … ⁀ B_n`, where `M⁻` is `M` without `C`.
-/

namespace DeadBms

/-- a rule set: bad root search, ascension rule and bracket function `f` -/
structure RuleSet where
  /-- bad root search: `badRoot M t` is the column index of the bad root -/
  badRoot : Mat → Nat → Option Nat
  /-- ascension flags: `ascend B x y = a'_{xy}` -/
  ascend : Mat → Nat → Nat → Bool
  /-- the bracket function `f` -/
  f : Nat → Nat

/-- one column of `B_k`: `b + k (a ⊗ Δ)`, `y` is the current row -/
def bumpCol (a : Nat → Bool) (Δ : Col) (k : Nat) : Nat → Col → Col
  | _, [] => []
  | y, v :: c => (v + if a y then k * ent Δ y else 0) :: bumpCol a Δ k (y + 1) c

/-- `B_k = B + k (A ⊗ Δ)`, `x` is the current column -/
def bumpMat (A : Nat → Nat → Bool) (Δ : Col) (k : Nat) : Nat → Mat → Mat
  | _, [] => []
  | x, b :: B => bumpCol (A x) Δ k 0 b :: bumpMat A Δ k (x + 1) B

/-- `B_1 ⁀ … ⁀ B_n` -/
def copies (B : Mat) (A : Nat → Nat → Bool) (Δ : Col) : Nat → Mat
  | 0 => []
  | n + 1 => copies B A Δ n ++ bumpMat A Δ (n + 1) 0 B

/-- one expansion step with `n` copies -/
def expand (R : RuleSet) (M : Mat) (n : Nat) : Mat :=
  match M.getLast? with
  | none => []
  | some C =>
    match lowestNZ C with
    | none => M.dropLast
    | some t =>
      match R.badRoot M t with
      | none => M.dropLast
      | some r =>
        let B := M.dropLast.drop r
        M.dropLast ++ copies B (R.ascend B) (delta t C (col M r)) n

/-- expansions with the brackets in a list -/
def runList (R : RuleSet) (M : Mat) : List Nat → Mat
  | [] => M
  | n :: ns => runList R (expand R M n) ns

/-- expansions with an arbitrary bracket sequence `ns 0, ns 1, …` -/
def run (R : RuleSet) : Mat → (Nat → Nat) → Nat → Mat
  | M, _, 0 => M
  | M, ns, i + 1 => run R (expand R M (ns 0)) (fun k => ns (k + 1)) i

/-- the computation of the page: `(M, n) ↦ (expand M (f n), f n)` -/
def compute (R : RuleSet) : Mat → Nat → Nat → Mat × Nat
  | M, n, 0 => (M, n)
  | M, n, i + 1 => compute R (expand R M (R.f n)) (R.f n) i

/-- the computation starting from `M[n]` reaches the empty matrix -/
def Halts (R : RuleSet) (M : Mat) (n : Nat) : Prop :=
  ∃ i, (compute R M n i).1 = []

/-- `A →_R B`: `B` is an expansion of `A` with some bracket -/
def Step (R : RuleSet) (A B : Mat) : Prop := ∃ n, B = expand R A n

/-- `M` is standard: `M`, with zero rows appended up to `N` rows, is reachable
from the `N`-row `(0,…,0)(1,…,1)` by expansions -/
def Std (R : RuleSet) (M : Mat) : Prop :=
  ∃ N ns, runList R (init N) ns = padM N M

end DeadBms
