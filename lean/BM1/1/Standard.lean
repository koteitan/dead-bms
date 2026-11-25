import Common.Rules

/-!
# BM1, example 1: standardness

`(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` (with a zero bottom row) is
reached from `(0,0,0,0)(1,1,1,1)` by the brackets below.
-/

namespace DeadBms.BM1.Ex1

/-- the example of hyp cos -/
def M : Mat := bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)]

/-- the brackets of the path from `(0,0,0,0)(1,1,1,1)` -/
def path : List Nat := [2, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 2]

theorem path_eq : runList BM1 (init 4) path = padM 4 M := by decide

theorem std : Std BM1 M := ⟨4, path, path_eq⟩

end DeadBms.BM1.Ex1
