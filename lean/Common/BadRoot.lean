import Common.Matrix

/-!
# Bad root search rules

A bad root rule receives the whole matrix `M` (its last column is `C`) and the
lowest nonzero row `t` of `C`, and returns the column index of the bad root.

* 左隣法 (left-adjacent method): the rightmost column `m` left of `C` with
  `m_y < c_y` for every `y ≤ t`.  (The page writes `m_y > c_y`; this is a
  typo, see `doc/rules.md`.)
* 上行枝無視方式 (Upper-Branch-Ignoring Model): the column of the parent of
  `c_t`, where the parent of the element at `(x, y)` is the rightmost element
  in row `y`, left of `x`, smaller than it, and (if `y > 0`) in the column of
  an ancestor of the element at `(x, y-1)`.
-/

namespace DeadBms

/-- 左隣法 -/
def leftAdj (M : Mat) (t : Nat) : Option Nat :=
  let C := col M (M.length - 1)
  findLastIdx (fun m => (List.range (t + 1)).all fun y => decide (ent m y < ent C y))
    M.dropLast

/-- `chain par fuel x = [x, par x, par (par x), …]` (the ancestors of `x`,
`x` itself included).  `fuel` bounds the length; `fuel = x` suffices because
`par` decreases. -/
def chain (par : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, x => [x]
  | fuel + 1, x =>
    x :: match par x with
      | none => []
      | some p => chain par fuel p

/-- parent in row 0: the rightmost column left of `x` with a smaller row-0 entry -/
def parent0 (M : Mat) (x : Nat) : Option Nat :=
  findLastIdx (fun m => decide (ent m 0 < ent (col M x) 0)) (M.take x)

/-- 上行枝無視方式: `parent M y x` is the column of the parent of the element at
column `x`, row `y`. -/
def parent (M : Mat) : Nat → Nat → Option Nat
  | 0, x => parent0 M x
  | y + 1, x =>
    (chain (parent M y) x x).tail.find? fun a =>
      decide (ent (col M a) (y + 1) < ent (col M x) (y + 1))

/-- 上行枝無視方式 bad root: the column of the parent of `c_t` -/
def ubim (M : Mat) (t : Nat) : Option Nat :=
  parent M t (M.length - 1)

end DeadBms
