import Common.Rules

/-!
Search for a standardness path: starting from `A = init N`, repeatedly
* if `A = M`, stop;
* if `M` is a proper prefix of `A`, expand with `[0]` (delete the last column);
* otherwise expand with the smallest `n` such that `A[n] ≥ M` in the
  lexicographic order.
-/

namespace DeadBms.Explore
open DeadBms

def colLt : Col → Col → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: c, b :: d => a < b || (a == b && colLt c d)

def matLt : Mat → Mat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: c, b :: d => colLt a b || (a == b && matLt c d)

partial def findPath (R : RuleSet) (M : Mat) (A : Mat) (fuel : Nat) (acc : List Nat) :
    Option (List Nat) :=
  if fuel = 0 then none
  else if A == M then some acc.reverse
  else if M.length < A.length && A.take M.length == M then
    findPath R M (expand R A 0) (fuel - 1) (0 :: acc)
  else
    match (List.range (M.length + 3)).find? (fun n => !(matLt (expand R A n) M)) with
    | none => none
    | some n => findPath R M (expand R A n) (fuel - 1) (n :: acc)

def padM (N : Nat) (M : Mat) : Mat := M.map fun c => c ++ List.replicate (N - c.length) 0

def path (R : RuleSet) (N : Nat) (M : Mat) : Option (List Nat) :=
  findPath R (padM N M) (init N) 100000 []

def checkPath (R : RuleSet) (N : Nat) (M : Mat) : String :=
  match path R N M with
  | none => "no path"
  | some ns => s!"len={ns.length} {ns}  ok={runList R (init N) ns == padM N M}"

/-- the computation with a constant bracket `n` -/
def trace (R : RuleSet) (M : Mat) (n steps : Nat) : List String :=
  (List.range steps).map fun i => showMat (run R M (fun _ => n) i)

end DeadBms.Explore

open DeadBms DeadBms.Explore

#eval checkPath BM1 4 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)]
#eval checkPath BM1 3 bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)]
#eval checkPath BM1_1 4 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,1)]
#eval checkPath BM2 5 bm[(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)]
#eval checkPath BM3 4 bm[(0,0,0)(1,1,1)(2,1,1)(1,1,1)]
