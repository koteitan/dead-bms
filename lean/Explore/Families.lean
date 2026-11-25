import Common.Rules

/-! Numerical check of the loop families: `next` is a prefix of `expand X n`. -/

namespace DeadBms.Explore
open DeadBms

def addC (v : Col) (c : Col) : Col := List.zipWith (· + ·) c (v ++ List.replicate c.length 0)
def blocks (k : Nat) (D : Mat) (v : Col) : Mat :=
  (List.range k).flatMap fun j => D.map (addC (v.map (j * ·)))

def isPrefix (Y X : Mat) : Bool := Y.length ≤ X.length && X.take Y.length == Y

/-- check `next X k` ⊑ `expand X n` for `k < K`, `n0 ≤ n ≤ 4` -/
def checkFam (R : RuleSet) (X next : Nat → Mat) (K n0 : Nat) : Bool :=
  (List.range K).all fun k => (List.range 5).all fun n => n < n0 || isPrefix (next k) (expand R (X k) n)

-- BM1/1 (hyp cos)
def b11 (k : Nat) : Mat :=
  bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)] ++ blocks k bm[(3,0,0)(2,1,0)] [0,0,0] ++ bm[(3,1,0)]
#eval checkFam BM1 b11 (fun k => b11 (k+1)) 8 1
#eval checkFam BM1 b11 (fun k => b11 (k+1)) 8 0

-- BM1/2 (Bubby3)
def b12 (k : Nat) : Mat :=
  bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)] ++ blocks k bm[(4,0)(3,1)] [0,0] ++ bm[(4,1)]
#eval checkFam BM1 b12 (fun k => b12 (k+1)) 8 1

-- BM1.1 (hyp cos): Q k = T_0 … T_k, six phases
def q (k : Nat) : Mat := (List.range (k+1)).flatMap fun j => [[j,j,0],[j+1,j+1,1],[j+2,0,0]]
def s (i k : Nat) : Mat :=
  match i with
  | 0 => q k ++ [[k+1,k+1,1]]
  | 1 => q k ++ [[k+1,k+1,0],[k+2,k+2,1],[k+3,1,0]]
  | 2 => q k ++ [[k+1,k+1,0],[k+2,k+2,1],[k+3,0,0],[k+4,1,1]]
  | 3 => q k ++ [[k+1,k+1,0],[k+2,k+2,1],[k+3,0,0],[k+4,1,0]]
  | 4 => q k ++ [[k+1,k+1,0],[k+2,k+2,1],[k+3,0,0],[k+4,0,0]]
  | _ => q k ++ [[k+1,k+1,0],[k+2,k+2,1],[k+3,0,0],[k+3,0,0]]
#eval (List.range 6).map fun i => checkFam BM1_1 (s i) (fun k => if i = 5 then s 0 (k+1) else s (i+1) k) 8 1
#eval showMat (s 0 0) ++ " / " ++ showMat (s 0 1)

-- BM2 (Bubby3)
def z (k : Nat) : Mat :=
  bm[(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)]
  ++ blocks k bm[(7,3,1,0)(8,4,2,1)(9,5,2,1)(10,6,2,1)(11,5,0,0)(12,4,1,1)] [6,2,0,0]
  ++ [[7+6*k, 3+2*k, 1, 1]]
#eval checkFam BM2 z (fun k => z (k+1)) 8 1
#eval showMat (z 2)

-- BM3 (Alemagno12)
def y3 (k : Nat) : Mat :=
  bm[(0,0,0)(1,1,1)(2,1,1)] ++ blocks k bm[(1,1,0)(2,2,1)] [2,0,0] ++ [[2*k+1, 1, 1]]
#eval checkFam BM3 y3 (fun k => y3 (k+1)) 8 1
#eval showMat (y3 3)

end DeadBms.Explore
