import DeadBms
open DeadBms

/-- the matrices on a standardness path -/
def states (R : RuleSet) (A : Mat) : List Nat → List Mat
  | [] => [A]
  | n :: ns => A :: states R (expand R A n) ns

def dump (tag : String) (Ms : List Mat) : IO Unit :=
  for M in Ms do IO.println s!"{tag} {showMat M}"

#eval dump "1.1" (states BM1_1 (init 4) BM1_1.Ex.path)
#eval dump "1.1" ((List.range 3).flatMap fun k =>
  [BM1_1.Ex.s0 k, BM1_1.Ex.s1 k, BM1_1.Ex.s2 k, BM1_1.Ex.s3 k, BM1_1.Ex.s4 k, BM1_1.Ex.s5 k])
#eval dump "2" (states BM2 (init 5) BM2.Ex.path)
#eval dump "2" ((List.range 3).map BM2.Ex.X)
