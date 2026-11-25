import Common.Rules

/-!
# BM3: standardness

`(0,0,0)(1,1,1)(2,1,1)(1,1,1)` (with a zero bottom row) is reached from
`(0,0,0,0)(1,1,1,1)` by the brackets below.
-/

namespace DeadBms.BM3.Ex

/-- the example of Alemagno12 -/
def M : Mat := bm[(0,0,0)(1,1,1)(2,1,1)(1,1,1)]

/-- the brackets of the path from `(0,0,0,0)(1,1,1,1)` -/
def path : List Nat := [2, 1, 1, 0, 2, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0]

theorem path_eq : runList BM3 (init 4) path = padM 4 M := by decide

theorem std : Std BM3 M := ⟨4, path, path_eq⟩

end DeadBms.BM3.Ex
