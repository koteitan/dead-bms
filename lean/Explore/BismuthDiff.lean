import «1y-bismuth».Model

/-!
Differential test of the Lean model of Bismuth against the Python port
(`tools/1y-bismuth/bismuth.py`).  Run through `tools/1y-bismuth/difftest.sh`,
which writes the test cases and passes their path in `DIFFTEST`.
-/

open Bismuth

def parseRow (s : String) : List Int := (s.splitOn ",").map fun t => (t.toInt?).getD 0

def showR : R (Row × Int) → String
  | .ok (r, n) => ",".intercalate (r.map toString) ++ " " ++ toString n
  | .err => "ERR"
  | .unsup => "UNSUP"
  | .div => "LOOP"

def diffTest : IO Unit := do
  let some path ← IO.getEnv "DIFFTEST" | IO.println "set DIFFTEST to the file of test cases"
  let lines ← IO.FS.lines path
  let mut bad := 0
  let mut n := 0
  for line in lines do
    match line.splitOn " " with
    | seq :: b :: rest =>
      n := n + 1
      let want := " ".intercalate rest
      let got := showR (main 3000 (parseRow seq) (b.toInt?.getD 0))
      if got != want then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"MISMATCH ({seq})[{b}]: lean={got} python={want}"
    | _ => pure ()
  IO.println s!"{n} cases, {bad} mismatches"

#eval diffTest
