import Common.Rules

/-!
# BM2: standardness

`(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)`
(with a zero bottom row) is reached from `(0,0,0,0,0)(1,1,1,1,1)` by the
brackets below.
-/

namespace DeadBms.BM2.Ex

/-- the example of Bubby3 -/
def M : Mat := bm[(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)]

/-- the brackets of the path from `(0,0,0,0,0)(1,1,1,1,1)` -/
def path : List Nat :=
  [2, 1, 1, 0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0,
    1, 1, 1, 1, 0]

theorem path_eq : runList BM2 (init 5) path = padM 5 M := by decide

theorem std : Std BM2 M := ⟨5, path, path_eq⟩

end DeadBms.BM2.Ex
