import Common.Rules

/-!
# BM1, example 2: standardness

`(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)` (with a zero bottom row) is reached
from `(0,0,0)(1,1,1)` by the brackets below.
-/

namespace DeadBms.BM1.Ex2

/-- the example of Bubby3 -/
def M : Mat := bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)]

/-- the brackets of the path from `(0,0,0)(1,1,1)` -/
def path : List Nat := [3, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2]

theorem path_eq : runList BM1 (init 3) path = padM 3 M := by decide

theorem std : Std BM1 M := ⟨3, path, path_eq⟩

end DeadBms.BM1.Ex2
