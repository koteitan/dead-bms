/-!
# Matrices

A Bashicu matrix is a list of columns, and a column is a list of natural
numbers.  Row 0 is the top row and column 0 is the leftmost column, so the
page's `c_y` (1-indexed) is `ent c (y-1)` here.

`bm[(0,0,0)(1,1,1)]` is notation for `[[0,0,0],[1,1,1]]`.
-/

namespace DeadBms

/-- A column (row 0 is the top row). -/
abbrev Col := List Nat

/-- A matrix as a list of columns (column 0 is the leftmost). -/
abbrev Mat := List Col

/-- entry of column `c` at row `y` (`0` outside the column) -/
def ent (c : Col) (y : Nat) : Nat := c.getD y 0

/-- column `x` of `M` (`[]` outside the matrix) -/
def col (M : Mat) (x : Nat) : Col := M.getD x []

/-- the index of the lowest nonzero row of `c` (the page's `t`, 0-indexed) -/
def lowestNZ : Col → Option Nat
  | [] => none
  | a :: c =>
    match lowestNZ c with
    | some t => some (t + 1)
    | none => if a = 0 then none else some 0

/-- the largest index `i` with `p l[i]` -/
def findLastIdx {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | a :: l =>
    match findLastIdx p l with
    | some i => some (i + 1)
    | none => if p a then some 0 else none

/-- `Δ`: `δ_y = c_y - r_y` for `y < t` and `δ_y = 0` for `y ≥ t` -/
def delta : Nat → Col → Col → Col
  | 0, c, _ => c.map fun _ => 0
  | _ + 1, [], _ => []
  | t + 1, a :: c, r => (a - r.headD 0) :: delta t c r.tail

/-- append zeros to a column up to `N` rows -/
def padCol (N : Nat) (c : Col) : Col := c ++ List.replicate (N - c.length) 0

/-- append zeros to every column up to `N` rows (BMS matrices are usually
written without their bottom zero rows) -/
def padM (N : Nat) (M : Mat) : Mat := M.map (padCol N)

/-- `(0,…,0)(1,…,1)` with `N` rows -/
def init (N : Nat) : Mat := [List.replicate N 0, List.replicate N 1]

/-- `(a,b,c)(d,e,f)` style rendering -/
def showMat (M : Mat) : String :=
  String.join (M.map fun c => "(" ++ ",".intercalate (c.map toString) ++ ")")

declare_syntax_cat bmcol
syntax "(" term,* ")" : bmcol

/-- `bm[(0,0,0)(1,1,1)]` is `[[0,0,0],[1,1,1]]`. -/
syntax "bm[" bmcol* "]" : term

macro_rules
  | `(bm[ $cs:bmcol* ]) => do
    let cols ← cs.mapM fun c =>
      match c with
      | `(bmcol| ( $xs,* )) => `(([$xs,*] : Col))
      | _ => Lean.Macro.throwUnsupported
    `(([$cols,*] : Mat))

end DeadBms
