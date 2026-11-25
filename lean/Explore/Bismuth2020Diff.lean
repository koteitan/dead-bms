import «1y-bismuth-2020-07-15».Model

/-!
Differential test of the Lean model of Bismuth (2020-07-15) against the Python
port (`tools/1y-bismuth-2020-07-15/bismuth.py`).  Run through
`tools/1y-bismuth-2020-07-15/difftest.sh`, which writes the test cases and passes
their path in `DIFFTEST`.  Cases where the Python port ran out of its step budget
(`BUDGET`) are skipped.
-/

open Bismuth Bismuth2020

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
      let want := " ".intercalate rest
      if want != "BUDGET" then
        n := n + 1
        let got := showR (Bismuth2020.main 3000 (parseRow seq) (b.toInt?.getD 0))
        if got != want then
          bad := bad + 1
          if bad ≤ 10 then IO.println s!"MISMATCH ({seq})[{b}]: lean={got} python={want}"
    | _ => pure ()
  IO.println s!"{n} cases, {bad} mismatches"

#eval diffTest
