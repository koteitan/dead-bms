import «1y-bismuth».Model

/-!
# Bismuth (version of 2020-07-15) as a Lean program

A line-by-line port of `src/io/github/syst3ms/bismuth/Bismuth.kt` at commit
`bf7ba654` (2020-07-14 21:25 UTC, "Fix diagonal finding&expansion method") of
https://github.com/Syst3ms/Bismuth.  Bismuth is defined by this program, so the
program is the definition being formalized.

## How the Kotlin program is modelled

* The generic parts (the outcome type `R`, array access, `resize`, `slice`,
  `paste`, `badRoot`, `List.copy`, bounded `while` loops) are those of the model
  of the version of 2019-09-29 (`«1y-bismuth».Model`); the Kotlin code of these
  functions is the same in both versions.
* Integers are the unbounded `Int`: Bismuth is read as a mathematical notation,
  not as a program with 32-bit integers.
* Every `while` and `do … while` loop and the recursion of `expand` get a step
  budget `fuel`; `div` means that the budget ran out.  The loop of
  `findParentIndex` always ends (its index decreases in every iteration), so it
  gets its own sufficient bound.
* Kotlin's `resize` shares the rows of the old matrix when the width is kept.
  This matters only in the expansion along the diagonal: when `tempValue`,
  `tempOffset` keep the width of `valueMat`, `offsetMat`, the first
  `min(height, newHeight)` rows are the same arrays, so every `paste` into
  `tempValue` (`tempOffset`) also changes `valueMat` (`offsetMat`), which the
  loop `for (i in newShape.indices)` reads again.  The model keeps both and
  copies the shared rows after every `paste` (`sync`).  (With the bracket 0 the
  width is always kept.)
* `assert` is disabled on the JVM by default, so it is omitted.
-/

namespace Bismuth2020

open Bismuth (R Row Mat aget aset mget mset first last copyOfRange width resize badRoot
  paste slice listCopy whileF removeLast)

/-! ## `findParentIndex` -/

/-- the `while (i >= 0)` loop of `findParentIndex`, with at most `fuel` iterations
(`fuel = i + 1` is enough, since `i` decreases by at least 1 in every iteration) -/
def fpiLoop (seq cur : Row) (current : Int) : Nat → Int → R (Option Int)
  | 0, i => if i < 0 then pure none else .unsup
  | f + 1, i =>
    if i < 0 then pure none else do
      let v ← aget seq i
      if 1 ≤ v ∧ v < current then pure (some i)
      else if v = 0 then pure none
      else do
        let o ← aget cur i
        fpiLoop seq cur current f (i - max o 1)

/-- `findParentIndex(seq, currentOffset, badRoot)` -/
def findParentIndex (seq cur : Row) (br : Option Int) : R (Option Int) := do
  let i : Int := br.getD ((seq.length : Int) - 1 - 1)
  let current ← last seq
  fpiLoop seq cur current (i.toNat + 1) i

/-! ## "Calculate differences and offsets" -/

/-- the state of the loop computing the differences -/
structure Mtn where
  vm : Mat
  om : Mat
  row : Nat
  deriving Repr, DecidableEq

/-- the condition `findParentIndex(valueMat.last(), offsetMat.last(), …) != null` -/
def mtnCond (st : Mtn) : R Bool := do
  let lv ← last st.vm
  let lo ← last st.om
  let br ← if st.row = 0 then pure none else some <$> badRoot st.om
  pure (← findParentIndex lv lo br).isSome

/-- `rowList.copyOfRange(0, i).all { it == 0 }` -/
def allZeroBefore (rowList : Row) (i : Int) : R Bool := do
  pure ((← copyOfRange rowList 0 i).all (· == 0))

/-- the body of the loop computing the differences (`fo` is `firstOffset`) -/
def mtnBody (fo : Option Row) (st : Mtn) : R Mtn := do
  let w ← width st.vm
  let mut vm ← resize st.vm w (st.vm.length + 1)
  let w' ← width st.om
  let mut om ← resize st.om w' (st.om.length + 1)
  let row : Int := st.row
  let w2 ← width vm
  for i' in [0:w2.toNat] do
    let i : Int := i'
    let rowList ← aget vm row
    match fo, st.row with
    | some f, 0 =>
      let a ← aget rowList i
      let fi ← aget f i
      let b ← aget rowList (i - fi)
      vm ← mset vm (row + 1) i (a - b)
      om ← mset om row i fi
    | _, _ =>
      let pre ← copyOfRange rowList 0 (i + 1)
      let orow ← aget om row
      let opre ← copyOfRange orow 0 (i + 1)
      let brp ← if st.row > 0 then do pure (some (i - max (← mget om (row - 1) i) 0))
        else pure none
      match ← findParentIndex pre opre brp with
      | none =>
        vm ← mset vm (row + 1) i 0
        let ri ← aget rowList i
        let z ← if ri = 0 then pure true else allZeroBefore rowList i
        om ← mset om row i (if z then 0 else -ri)
      | some p =>
        let a ← aget rowList i
        let b ← aget rowList p
        vm ← mset vm (row + 1) i (a - b)
        om ← mset om row i (i - p)
  pure { vm := vm, om := om, row := st.row + 1 }

/-- "Calculate differences and offsets" -/
def mountain (fuel : Nat) (seq : Row) (fo : Option Row) : R Mtn :=
  whileF mtnCond (mtnBody fo) fuel { vm := [seq], om := [List.replicate seq.length 0], row := 0 }

/-! ## `copyOffset` -/

/-- `for (k in result.indices) { val toCopy = result[k][badRoot + j + 1];
result[k][target] = toCopy + (if (j - toCopy + 1 < 0) copyWidth * i else 0) }` -/
def copyCol (br copyW i j target : Int) : List Nat → Mat → R Mat
  | [], res => pure res
  | k :: ks, res => do
    let toCopy ← mget res k (br + j + 1)
    let v := toCopy + (if j - toCopy + 1 < 0 then copyW * i else 0)
    copyCol br copyW i j target ks (← mset res k target v)

/-- the loop `for (j in 0 until copyWidth)` of `copyOffset`, over the remaining `j`s -/
def copyBlockAux (br copyW newW i : Int) : List Nat → Mat → R Mat
  | [], res => pure res
  | j :: js, res =>
    let target := br + copyW * i + j + 1
    if target ≥ newW then pure res
    else do copyBlockAux br copyW newW i js (← copyCol br copyW i j target (List.range res.length) res)

/-- one iteration of the `while` loop of `copyOffset` -/
def copyBlock (res : Mat) (br copyW newW i : Int) : R Mat :=
  copyBlockAux br copyW newW i (List.range copyW.toNat) res

/-- the condition `result.first().last() == 0` of the `while` loop of `copyOffset` -/
def coCond (st : Mat × Int) : R Bool := do pure ((← last (← first st.1)) == 0)

/-- the body of the `while` loop of `copyOffset` (`st.2` is `i`) -/
def coBody (br copyW newW : Int) (st : Mat × Int) : R (Mat × Int) := do
  pure (← copyBlock st.1 br copyW newW st.2, st.2 + 1)

/-- `Matrix.copyOffset(badRoot, times)` (every call of the program passes `times`) -/
def copyOffset (fuel : Nat) (m : Mat) (br times : Int) : R Mat := do
  let w ← width m
  let copyW := w - br - 1
  let newW := br + copyW * times + 1
  let res ← resize m newW m.length
  let st ← whileF coCond (coBody br copyW newW) fuel (res, 1)
  pure st.1

/-! ## the expansion without a diagonal -/

/-- `refillMatrix(valueMat, offsetMat)` -/
def refill (vm om : Mat) : R Mat := do
  let mut vm := vm
  for i' in [0:vm.length - 1] do
    let i : Int := (vm.length : Int) - 2 - i'
    let w ← width vm
    for j' in [0:w.toNat] do
      let j : Int := j'
      let off ← mget om i j
      if off < 0 then
        vm ← mset vm i j (-off)
      else
        let below ← if i + 1 < vm.length then mget vm (i + 1) j else pure 0
        let v ← mget vm i (j - off)
        vm ← mset vm i j (below + v)
  pure vm

/-- the result of `expand` (`ExpansionResult`) -/
structure Exp where
  vm : Mat
  om : Mat
  br : Int
  deriving Repr, DecidableEq

/-- the expansion without a diagonal after "Copy offsets" ("Copy bad part") -/
def normalRest (vm om : Mat) (br times : Int) : R Exp := do
  let mut vm := vm
  for i in [0:vm.length] do
    let w ← width vm
    vm ← mset vm i (w - 1) 0
  let w ← width vm
  let bpw := w - br - 1
  let newW := br + bpw * times
  vm ← resize vm newW vm.length
  for i in [1:times.toNat] do
    for j in [0:bpw.toNat] do
      for k in [0:vm.length] do
        let x := br + j
        if (← mget om k x) == 0 then
          let c2 ← if k > 0 then do pure (decide (x - (← mget om (k - 1) x) < br)) else pure false
          if !c2 then
            vm ← mset vm k (x + bpw * i) (← mget vm k x)
  let v ← refill vm om
  pure { vm := v, om := om, br := br }

/-- the expansion without a diagonal ("Copy offsets", "Copy bad part") -/
def normal (fuel : Nat) (vm om : Mat) (br times : Int) : R Exp := do
  let om ← copyOffset fuel om br times
  normalRest vm om br times

/-! ## the expansion along the diagonal -/

/-- `c.indexOfLast { it > 0 }` -/
def indexOfLastPos (c : Row) : Int :=
  match ((List.range c.length).filter fun (k : Nat) => c.getD k 0 > 0).getLast? with
  | some k => k
  | none => -1

/-- `(0 until valueMat.width).map { i -> valueMat.map { it[i] } }.mapIndexed { i, c -> i to c.indexOfLast { it > 0 } }` -/
def rootsOf (vm : Mat) : R (List (Int × Int)) := do
  let w ← width vm
  (List.range w.toNat).mapM fun (i : Nat) => do
    let col ← vm.mapM fun row => aget row i
    pure ((i : Int), indexOfLastPos col)

/-- `roots.map { valueMat[it.second][it.first] }` -/
def diagonalOf (vm : Mat) (roots : List (Int × Int)) : R Row :=
  roots.mapM fun r => mget vm r.2 r.1

/-- `roots.zipWithNext { f, s -> s.second - f.second }` -/
def shapeOf (roots : List (Int × Int)) : List Int :=
  (roots.zip roots.tail).map fun p => p.2.2 - p.1.2

/-- `l.indexOf(c)` (`-1` if absent) -/
def indexOf (l : List (Int × Int)) (c : Int × Int) : Int :=
  match l with
  | [] => -1
  | a :: as => if a = c then 0 else
    let k := indexOf as c
    if k < 0 then -1 else k + 1

/-- the state of `do { … } while (…)` computing `forcedOffset[i]`: the point `c`,
and whether `continue@diag` was reached -/
structure FO where
  c : Int × Int
  done : Bool
  deriving Repr, DecidableEq

/-- the body of `do { … } while (…)`:
`if (c == 0 to 0) { …; continue@diag }; c -= if (…) offsetMat[c.second][c.first] to 0 else offsetMat[c.second - 1][c.first] to 1` -/
def foBody (vm om : Mat) (st : FO) : R FO :=
  if st.c = (0, 0) then pure { c := st.c, done := true } else do
    let y := st.c.2 + 1
    let bv ← if 0 ≤ y ∧ y < vm.length then mget vm y st.c.1 else pure 0
    let d ← if bv > 0 then do pure ((← mget om st.c.2 st.c.1), (0 : Int))
      else do pure ((← mget om (st.c.2 - 1) st.c.1), (1 : Int))
    pure { c := (st.c.1 - d.1, st.c.2 - d.2), done := false }

/-- the condition `valueMat[c.second + 1][c.first] > 0 || valueMat[c.second][c.first] >= diagonal[i]`
(and `false` after `continue@diag`) -/
def foCond (vm : Mat) (di : Int) (st : FO) : R Bool :=
  if st.done then pure false else do
    if (← mget vm (st.c.2 + 1) st.c.1) > 0 then pure true
    else pure (decide ((← mget vm st.c.2 st.c.1) ≥ di))

/-- `forcedOffset[i] = if (i == 0) 0 else -diagonal[i]` after `continue@diag`,
`forcedOffset[i] = i - roots.indexOf(c)` otherwise -/
def foResult (roots : List (Int × Int)) (i : Nat) (di : Int) (st : FO) : Int :=
  if st.done then (if i = 0 then 0 else -di) else (i : Int) - indexOf roots st.c

/-- `forcedOffset[i]`, computed by `do { … } while (…)` -/
def forcedAt (fuel : Nat) (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row) (i : Nat) :
    R Int := do
  let r ← aget roots i
  let di ← aget diagonal i
  let st ← foBody vm om { c := r, done := false }
  let st ← whileF (foCond vm di) (foBody vm om) fuel st
  pure (foResult roots i di st)

/-- `diag@for (i in roots.indices) { … }` -/
def forcedList (fuel : Nat) (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row) :
    List Nat → R (List Int)
  | [] => pure []
  | i :: is => do
    let a ← forcedAt fuel vm om roots diagonal i
    let as ← forcedList fuel vm om roots diagonal is
    pure (a :: as)

/-- the data computed after the recursive expansion, before `copyOffset` of the bad part -/
structure Pre1 where
  newShape : List Int
  newRoots : List (Int × Int)
  nb : Int × Int
  newDiagonal : Row
  tempV : Mat
  tempO : Mat
  badX : Int
  badY : Int
  bp : Mat
  deriving Repr, DecidableEq

/-- `newShape`, …, `tempOffset`, `(badX, badY)` and the bad part of `offsetMat` -/
def diagPre (om vm : Mat) (shape : List Int) (roots : List (Int × Int)) (ed : Exp) (times : Int) :
    R Pre1 := do
  let newShape ← listCopy shape ed.br times
  let newRoots ← listCopy roots ed.br times
  let nb : Int × Int := (newShape.length, newShape.sum)
  let newDiagonal ← first ed.vm
  let tempV ← resize vm (nb.1 + 1) (nb.2 + 1)
  let tempO ← resize om (nb.1 + 1) (nb.2 + 1)
  let bxy ← aget roots ed.br
  let w ← width om
  let bp ← slice om bxy.1 bxy.2 (w - 1) bxy.2
  pure { newShape := newShape, newRoots := newRoots, nb := nb, newDiagonal := newDiagonal,
         tempV := tempV, tempO := tempO, badX := bxy.1, badY := bxy.2, bp := bp }

/-- the data used by `for (i in newShape.indices)` -/
structure Prep where
  newShape : List Int
  newRoots : List (Int × Int)
  newDiagonal : Row
  tempV : Mat
  tempO : Mat
  badX : Int
  badY : Int
  badPart : Mat
  /-- the number of rows that `valueMat` and `tempValue` share (see the header) -/
  shareV : Nat
  /-- the number of rows that `offsetMat` and `tempOffset` share -/
  shareO : Nat
  deriving Repr, DecidableEq

/-- the number of rows shared by `m` and `m.resize(newW, newH)` -/
def shared (m : Mat) (newW newH : Int) : R Nat := do
  if newW = (← width m) then pure (min m.length newH.toNat) else pure 0

/-- the rows `0 … k - 1` of `old` are the arrays of `new` -/
def sync (old new : Mat) (k : Nat) : Mat := new.take k ++ old.drop k

/-- after `copyOffset` of the bad part -/
def diagPost (vm om : Mat) (x : Pre1) (badPart : Mat) : R Prep := do
  let sv ← shared vm (x.nb.1 + 1) (x.nb.2 + 1)
  let so ← shared om (x.nb.1 + 1) (x.nb.2 + 1)
  pure { newShape := x.newShape, newRoots := x.newRoots, newDiagonal := x.newDiagonal,
         tempV := x.tempV, tempO := x.tempO, badX := x.badX, badY := x.badY, badPart := badPart,
         shareV := sv, shareO := so }

/-- "Calculate the new diagonal" up to `badPartOffset` -/
def diagPrep (fuel : Nat) (vm om : Mat) (shape : List Int) (roots : List (Int × Int)) (ed : Exp)
    (times : Int) : R Prep := do
  let x ← diagPre om vm shape roots ed times
  let badPart ← copyOffset fuel x.bp 0 times
  diagPost vm om x badPart

/-- the state of `for (i in newShape.indices)`, with the current `valueMat`, `offsetMat` -/
structure SL where
  tempV : Mat
  tempO : Mat
  vm : Mat
  om : Mat
  row : Int
  deriving Repr, DecidableEq

/-- the values computed in one iteration of `for (i in newShape.indices)` before the
branch on `offsetPart` -/
structure SPre where
  i : Nat
  s : Int
  tempV : Mat
  vm : Mat
  opart : Mat
  deriving Repr, DecidableEq

/-- one iteration of `for (i in newShape.indices)`, up to `offsetPart` -/
def shapePre (p : Prep) (i : Nat) (st : SL) : R SPre := do
  let s ← aget p.newShape i
  let r ← aget p.newRoots i
  let vpart ← slice st.vm r.1 (min r.2 (r.2 + s)) (r.1 + 1) (max r.2 (r.2 + s))
  let vpart ← mset vpart (-(min s 0)) 0 (← aget p.newDiagonal i)
  let tempV ← paste st.tempV vpart i (st.row + min s 0)
  let w ← width st.om
  let opart ← slice st.om r.1 r.2 (w - 1) (r.2 + max s 0)
  pure { i := i, s := s, tempV := tempV, vm := sync st.vm tempV p.shareV, opart := opart }

/-- `offsetPart.resize(tempOffset.width - i, offsetPart.size).paste(badPartOffset.slice(1, 0, badPartOffset.width - 1, 0), offsetPart.width, 0)` -/
def shapeBad (p : Prep) (st : SL) (x : SPre) : R Mat := do
  let tw ← width st.tempO
  let o1 ← resize x.opart (tw - x.i) x.opart.length
  let bw ← width p.badPart
  let bs ← slice p.badPart 1 0 (bw - 1) 0
  let ow ← width x.opart
  paste o1 bs ow 0

/-- `if (row >= badY && s > 0) … else if (s > 0) offsetPart = offsetPart.copyOffset(badX - i, times)` -/
def shapeMid (fuel : Nat) (p : Prep) (times : Int) (st : SL) (x : SPre) : R Mat :=
  if st.row ≥ p.badY ∧ x.s > 0 then shapeBad p st x
  else if x.s > 0 then copyOffset fuel x.opart (p.badX - x.i) times
  else pure x.opart

/-- the rest of one iteration of `for (i in newShape.indices)` -/
def shapePost (p : Prep) (st : SL) (x : SPre) (opart : Mat) : R SL := do
  let tempO ← paste st.tempO opart x.i st.row
  pure { tempV := x.tempV, tempO := tempO, vm := x.vm, om := sync st.om tempO p.shareO,
         row := st.row + x.s }

/-- one iteration of `for (i in newShape.indices)` -/
def shapeStep (fuel : Nat) (p : Prep) (times : Int) (i : Nat) (st : SL) : R SL := do
  let x ← shapePre p i st
  let o ← shapeMid fuel p times st x
  shapePost p st x o

/-- `for (i in newShape.indices)` -/
def shapeLoop (fuel : Nat) (p : Prep) (times : Int) : List Nat → SL → R SL
  | [], st => pure st
  | i :: is, st => do shapeLoop fuel p times is (← shapeStep fuel p times i st)

/-- the end of the expansion along the diagonal -/
def diagEnd (p : Prep) (st : SL) (br : Int) : R Exp := do
  let tempV ← mset st.tempV st.row p.newShape.length (← aget p.newDiagonal p.newShape.length)
  let v ← refill tempV st.tempO
  pure { vm := v, om := st.tempO, br := br }

/-- `lastRow.last() > 1` where `lastRow = valueMat.last()` -/
def isDiag (mt : Mtn) : R Bool := do
  let lastRow ← last mt.vm
  pure (decide ((← last lastRow) > 1))

/-- the initial state of `for (i in newShape.indices)` -/
def initSL (vm om : Mat) (p : Prep) : SL := { tempV := p.tempV, tempO := p.tempO, vm := vm, om := om, row := 0 }

/-- `expand(seq, times, firstOffset)` -/
def expand : Nat → Row → Int → Option Row → R Exp
  | 0, _, _, _ => .div
  | f + 1, seq, times, fo => do
    let mt ← mountain (f + 1) seq fo
    let br ← badRoot mt.om
    if ← isDiag mt then
      let roots ← rootsOf mt.vm
      let diagonal ← diagonalOf mt.vm roots
      let shape := shapeOf roots
      let forced ← forcedList (f + 1) mt.vm mt.om roots diagonal (List.range roots.length)
      let roots' ← removeLast roots
      let ed ← expand f diagonal (times + 1) (some forced)
      let p ← diagPrep (f + 1) mt.vm mt.om shape roots' ed times
      let st ← shapeLoop (f + 1) p times (List.range p.newShape.length) (initSL mt.vm mt.om p)
      diagEnd p st br
    else
      normal (f + 1) mt.vm mt.om br times

/-- `main`: the output for the input `(seq)[n]` -/
def main (fuel : Nat) (seq : Row) (n : Int) : R (Row × Int) := do
  if (← last seq) == 1 then pure (seq.dropLast, n + 1)
  else do
    let e ← expand fuel seq (n + 1) none
    pure (← first e.vm, n)

end Bismuth2020
