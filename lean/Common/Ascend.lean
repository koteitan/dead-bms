import Common.BadRoot

/-!
# Bad part ascension rules

An ascension rule receives the bad part `B` (column 0 of `B` is the bad root)
and returns the flag `a'_{xy}` (column `x` of `B`, row `y`).  Every rule set in
this project uses 改変なし (no modification), so `a_{xy} = a'_{xy}`.

* 全枝有効方式: `a'_{xy} = 1` for all `x, y`.
* BM2 方式: `a'_{0y} = 1`, and for `x > 0`
  `a'_{xy} = 1 ↔ a'_{p(x)y} = 1 ∧ r_y < b_{xy}`,
  where `r_y = b_{0y}` is the bad root (the page writes `b_{r_y y}`).
* BM3 方式: `a'_{x0} = 1`, `a'_{0y} = 1`, and for `x > 0`
  `a'_{xy} = 1 ↔ a'_{p(x)y} = 1 ∧ b_{p(x)y} < b_{xy}`.

Here `p(x) = max {k | k < x ∧ b_{k0} < b_{x0}}`.  When `p(x)` does not exist
the flag is `0` (this does not happen in a bad part whose row-0 entries right
of the root exceed the root's).
-/

namespace DeadBms

/-- 全枝有効方式 -/
def ascAll (_B : Mat) (_x _y : Nat) : Bool := true

/-- `p(x)`: the left-adjacent parent of column `x` of `B` in row 0 -/
def pLeft (B : Mat) (x : Nat) : Option Nat := parent0 B x

/-- BM2 方式, with fuel -/
def ascBM2Aux (B : Mat) (y : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | fuel + 1, x + 1 =>
    match pLeft B (x + 1) with
    | none => false
    | some k => ascBM2Aux B y fuel k && decide (ent (col B 0) y < ent (col B (x + 1)) y)

/-- BM2 方式 -/
def ascBM2 (B : Mat) (x y : Nat) : Bool := ascBM2Aux B y x x

/-- BM3 方式, with fuel -/
def ascBM3Aux (B : Mat) (y : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | fuel + 1, x + 1 =>
    match pLeft B (x + 1) with
    | none => false
    | some k => ascBM3Aux B y fuel k && decide (ent (col B k) y < ent (col B (x + 1)) y)

/-- BM3 方式 -/
def ascBM3 (B : Mat) (x y : Nat) : Bool := y == 0 || ascBM3Aux B y x x

end DeadBms
