import DeadBms
open DeadBms

/-- the matrices on a path, with the bottom row dropped -/
def show1 (R : RuleSet) (A : Mat) (ns : List Nat) : IO Unit := do
  let mut M := A
  IO.println s!"  {showMat (M.map List.dropLast)}"
  for n in ns do
    M := expand R M n
    IO.println s!"[{n}] {showMat (M.map List.dropLast)}"

#eval show1 BM1 (init 4) BM1.Ex1.path
#eval IO.println "----"
#eval show1 BM1 (init 3) BM1.Ex2.path
#eval IO.println "----"
#eval show1 BM1_1 (init 4) BM1_1.Ex.path
#eval IO.println "----"
#eval show1 BM2 (init 5) BM2.Ex.path
#eval IO.println "----"
#eval show1 BM3 (init 4) BM3.Ex.path
