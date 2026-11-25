/-!
# Bismuth (version of 2019-09-29) as a Lean program

A line-by-line port of `src/io/github/syst3ms/bismuth/Bismuth.kt` at commit
`5e4c65c3` (2019-09-29, "Fixed small expansion quick") of
https://github.com/Syst3ms/Bismuth.  Bismuth is defined by this program, so the
program is the definition being formalized.

## How the Kotlin program is modelled

* Arrays are lists.  Every array access goes through `aget` / `aset`, which
  return `err` where Kotlin throws (index out of bounds, `first()` / `last()`
  of an empty array, `subList` / `copyOfRange` with bad bounds).
* `Int` is modelled by the unbounded `Int`.  (All numbers in the computations
  below are small.)
* Every `while` loop and the recursion of `expand` get a step budget `fuel`.
  `div` means that the budget ran out.  A run of the Kotlin program terminates
  iff the model returns something other than `div` for some `fuel`;
  a proof of `∀ fuel, … = div` is a proof that the Kotlin program runs forever.
* The model is pure, whereas Kotlin arrays are mutable and `resize` can share
  rows between the old and the new matrix.  Sharing changes the result only in
  the diagonal expansion, when `resize` keeps the width (then pasting into
  `tempValue` also writes into `valueMat`).  The model returns `unsup` in that
  case instead of guessing, and the theorems show that it does not occur.
* `assert` is disabled on the JVM by default, so it is omitted.
-/

namespace Bismuth

/-- the outcome of running (a part of) the program -/
inductive R (α : Type) where
  /-- finished with a value -/
  | ok : α → R α
  /-- the Kotlin program throws an exception -/
  | err : R α
  /-- a case where row sharing could make Kotlin differ from the pure model -/
  | unsup : R α
  /-- the step budget ran out -/
  | div : R α
  deriving Repr, DecidableEq

instance : Monad R where
  pure := .ok
  bind m k := match m with
    | .ok a => k a
    | .err => .err
    | .unsup => .unsup
    | .div => .div

/-- a row of a matrix -/
abbrev Row := List Int

/-- a matrix as a list of rows (`Array<Array<Int>>`) -/
abbrev Mat := List Row

/-! ## arrays -/

/-- `l[i]` -/
def aget {α : Type} (l : List α) (i : Int) : R α :=
  if 0 ≤ i then
    match l[i.toNat]? with
    | some a => .ok a
    | none => .err
  else .err

/-- `l[i] = a` -/
def aset {α : Type} (l : List α) (i : Int) (a : α) : R (List α) :=
  if 0 ≤ i ∧ i.toNat < l.length then .ok (l.set i.toNat a) else .err

/-- `m[r][c]` -/
def mget (m : Mat) (r c : Int) : R Int := do aget (← aget m r) c

/-- `m[r][c] = v` -/
def mset (m : Mat) (r c v : Int) : R Mat := do
  let row ← aget m r
  let row ← aset row c v
  aset m r row

/-- `first()` -/
def first {α : Type} : List α → R α
  | a :: _ => .ok a
  | [] => .err

/-- `last()` -/
def last {α : Type} (l : List α) : R α :=
  match l.getLast? with
  | some a => .ok a
  | none => .err

/-- `copyOfRange(a, b)` and `subList(a, b)` -/
def copyOfRange {α : Type} (l : List α) (a b : Int) : R (List α) :=
  if 0 ≤ a ∧ a ≤ b ∧ b ≤ l.length then .ok ((l.drop a.toNat).take (b - a).toNat) else .err

/-- `Matrix.width` (`this[0].size`) -/
def width (m : Mat) : R Int := do pure ((← aget m 0).length : Int)

/-- `Matrix.resize(newWidth, newHeight)` -/
def resize (m : Mat) (newW newH : Int) : R Mat := do
  let w ← width m
  let h : Int := m.length
  let r1 : Mat :=
    if h < newH then m ++ List.replicate (newH - h).toNat (List.replicate w.toNat 0)
    else if newH < h then m.take (m.length - (h - newH).toNat)
    else m
  pure <|
    if w < newW then r1.map (fun row => row ++ List.replicate (newW - w).toNat 0)
    else if newW < w then r1.map (fun row => row.take (row.length - (w - newW).toNat))
    else r1

/-- `Matrix.badRoot` (`width - this[size - 2][width - 1] - 1`) -/
def badRoot (m : Mat) : R Int := do
  let w ← width m
  let v ← mget m ((m.length : Int) - 2) (w - 1)
  pure (w - v - 1)

/-- `Matrix.paste(part, x, y)` -/
def paste (m part : Mat) (x y : Int) : R Mat := do
  let mut m := m
  for i in [0:part.length] do
    if y + i ≥ m.length then break
    let pw ← width part
    for j in [0:pw.toNat] do
      if x + j ≥ (← width m) then break
      m ← mset m (y + i) (x + j) (← mget part i j)
  pure m

/-- `Matrix.slice(x, y, x1, y1)` -/
def slice (m : Mat) (x y x1 y1 : Int) : R Mat := do
  let rows ← copyOfRange m y (y1 + 1)
  rows.mapM fun r => copyOfRange r x (x1 + 1)

/-- `List.copy(root, times)` -/
def listCopy {α : Type} (l : List α) (root times : Int) : R (List α) := do
  let a ← copyOfRange l 0 root
  let b ← copyOfRange l root l.length
  pure (a ++ (List.replicate times.toNat b).flatten)

/-! ## loops -/

/-- `while (cond(s)) s = body(s)`, with at most `fuel` iterations -/
def whileF {σ : Type} (cond : σ → R Bool) (body : σ → R σ) : Nat → σ → R σ
  | 0, s => do if ← cond s then .div else pure s
  | f + 1, s => do if ← cond s then whileF cond body f (← body s) else pure s

/-! ## the functions of the program -/

/-- `findParentIndex(seq, badRoot)` -/
def findParentIndex (seq : Row) (br : Option Int) : Option Int :=
  let lst := seq.getLastD 0
  ((List.range (seq.length - 1)).reverse.find? fun i =>
    !(seq.getD i 0 == 0 || decide (seq.getD i 0 ≥ lst) ||
      (match br with
        | some b => decide ((i : Int) > b)
        | none => false))).map fun i => (i : Int)

/-- `refillMatrix(valueMat, offsetMat)` -/
def refill (vm om : Mat) : R Mat := do
  let mut vm := vm
  for i' in [0:vm.length] do
    let i : Int := (vm.length : Int) - 1 - i'
    let w ← width vm
    for j' in [0:w.toNat] do
      let j : Int := j'
      let below ← if i + 1 < vm.length then mget vm (i + 1) j else pure 0
      let off ← mget om i j
      let v ← mget vm i (j - off)
      vm ← mset vm i j (below + v)
  pure vm

/-- `for (k in result.indices) result[k][target] = result[k][src]` -/
def copyCol (src target : Int) : List Nat → Mat → R Mat
  | [], res => pure res
  | k :: ks, res => do
    let v ← mget res k src
    copyCol src target ks (← mset res k target v)

/-- the loop `for (j in 0 until copyWidth)` of `copyOffset`, over the remaining `j`s -/
def copyBlockAux (br copyW newW i : Int) : List Nat → Mat → R Mat
  | [], res => pure res
  | j :: js, res =>
    let target := br + copyW * i + j + 1
    if target ≥ newW then pure res
    else do copyBlockAux br copyW newW i js (← copyCol (br + j + 1) target (List.range res.length) res)

/-- one iteration of the `while` loop of `copyOffset`:
`for (j in 0 until copyWidth) { val target = …; if (target >= newWidth) break; … }` -/
def copyBlock (res : Mat) (br copyW newW i : Int) : R Mat :=
  copyBlockAux br copyW newW i (List.range copyW.toNat) res

/-- the condition `result.first().last() == 0` of the `while` loop of `copyOffset` -/
def coCond (st : Mat × Int) : R Bool := do pure ((← last (← first st.1)) == 0)

/-- the body of the `while` loop of `copyOffset` (`st.2` is `i`) -/
def coBody (br copyW newW : Int) (st : Mat × Int) : R (Mat × Int) := do
  pure (← copyBlock st.1 br copyW newW st.2, st.2 + 1)

/-- `newWidth` of `copyOffset` -/
def coNewW (br copyW : Int) : Option Int → Option Int → R Int
  | some t, _ => pure (br + copyW * t + 1)
  | none, some s => pure s
  | none, none => .err

/-- `Matrix.copyOffset(badRoot, times, size)` -/
def copyOffset (fuel : Nat) (m : Mat) (br : Int) (times size : Option Int) : R Mat := do
  let w ← width m
  let copyW := w - br - 1
  let newW ← coNewW br copyW times size
  let res ← resize m newW m.length
  let st ← whileF coCond (coBody br copyW newW) fuel (res, 1)
  pure st.1

/-- the state of the loop computing the differences -/
structure Mtn where
  vm : Mat
  om : Mat
  row : Nat
  deriving Repr, DecidableEq

/-- the condition `findParentIndex(valueMat.last(), …) != null` -/
def mtnCond (st : Mtn) : R Bool := do
  let lr ← last st.vm
  let br ← if st.row = 0 then pure none else some <$> badRoot st.om
  pure (findParentIndex lr br).isSome

/-- the body of the loop computing the differences -/
def mtnBody (st : Mtn) : R Mtn := do
  let w ← width st.vm
  let mut vm ← resize st.vm w (st.vm.length + 1)
  let w' ← width st.om
  let mut om ← resize st.om w' (st.om.length + 1)
  let row : Int := st.row
  let w2 ← width vm
  for i' in [0:w2.toNat] do
    let i : Int := i'
    let rowList ← aget vm row
    let pre ← copyOfRange rowList 0 (i + 1)
    let brp ← if st.row > 0 then do pure (some (i - (← mget om (row - 1) i))) else pure none
    match findParentIndex pre brp with
    | none =>
      vm ← mset vm (row + 1) i 0
      om ← mset om row i 0
    | some p =>
      let diff := (← aget rowList i) - (← aget rowList p)
      vm ← mset vm (row + 1) i diff
      om ← mset om row i (i - p)
  pure { vm := vm, om := om, row := st.row + 1 }

/-- "Calculate differences and offsets" -/
def mountain (fuel : Nat) (seq : Row) : R Mtn :=
  whileF mtnCond mtnBody fuel { vm := [seq], om := [List.replicate seq.length 0], row := 0 }

/-- the result of `expand` (`ExpansionResult`) -/
structure Exp where
  vm : Mat
  om : Mat
  br : Int
  deriving Repr, DecidableEq

/-- `indexOfLast { it == x }` of `l.mapIndexed { i, e -> i - e }` (`-1` if none) -/
def lastParentIndex (l : Row) (x : Int) : Int :=
  let ps := (List.range l.length).filter fun (i : Nat) => (i : Int) - l.getD i 0 == x
  match ps.getLast? with
  | some i => i
  | none => -1

/-- `valueMat.getOrNull(y)?.getOrNull(x) ?: 0` -/
def getOrZero (m : Mat) (y x : Int) : Int :=
  if 0 ≤ y ∧ 0 ≤ x then ((m[y.toNat]?).bind fun r => r[x.toNat]?).getD 0 else 0

/-- the state of the loop walking along the diagonal -/
structure Walk where
  shape : List (Int × Int)
  diagonal : Row
  cx : Int
  cy : Int
  deriving Repr, DecidableEq

/-- the condition `coords.first < valueMat.width` -/
def walkCond (vm : Mat) (st : Walk) : R Bool := do pure (decide (st.cx < (← width vm)))

/-- the body of the loop walking along the diagonal -/
def walkBody (vm om : Mat) (st : Walk) : R Walk := do
  let d ← mget vm st.cy st.cx
  let diagonal := st.diagonal ++ [d]
  if getOrZero vm (st.cy + 1) (st.cx + 1) > 0 then
    let orow ← aget om st.cy
    let root := lastParentIndex orow st.cx - st.cx
    pure { shape := st.shape ++ [(root, 1)], diagonal := diagonal, cx := st.cx + root, cy := st.cy + 1 }
  else
    pure { shape := st.shape ++ [(1, 0)], diagonal := diagonal, cx := st.cx + 1, cy := st.cy }

/-- "Calculate diagonal shape & offsets" -/
def walk (fuel : Nat) (vm om : Mat) : R Walk :=
  whileF (walkCond vm) (walkBody vm om) fuel { shape := [], diagonal := [], cx := 0, cy := 0 }

/-- `shape.removeAt(shape.lastIndex)` -/
def removeLast {α : Type} (l : List α) : R (List α) :=
  if l = [] then .err else .ok l.dropLast

/-- `shape.mapIndexed { i, _ -> shape.subList(0, i).fold(0 to 0, Pair::plus) }` -/
def prefixSums (shape : List (Int × Int)) : List (Int × Int) :=
  (List.range shape.length).map fun i =>
    ((shape.take i).foldl (fun a e => (a.1 + e.1, a.2 + e.2)) (0, 0))

/-- the data computed after the recursive expansion of the diagonal -/
structure Prep where
  newShape : List (Int × Int)
  newRoots : List (Int × Int)
  newDiagonal : Row
  tempV : Mat
  tempO : Mat
  deriving Repr, DecidableEq

/-- "Calculate the new diagonal" and the initial `tempValue`, `tempOffset` -/
def diagPrep (vm om : Mat) (shape : List (Int × Int)) (ed : Exp) (times : Int) : R Prep := do
  let roots := prefixSums shape
  let newShape ← listCopy shape ed.br (times + 1)
  let newRoots ← listCopy roots ed.br (times + 1)
  let nb : Int × Int := ((newShape.map Prod.fst).sum, (newShape.map Prod.snd).sum)
  let newDiagonal ← first ed.vm
  -- `resize` keeps the width: Kotlin shares the rows of `valueMat` with `tempValue`
  if nb.1 + 1 = (← width vm) then .unsup else
  let tempV ← resize vm (nb.1 + 1) (nb.2 + 1)
  let tempO ← resize om (nb.1 + 1) (nb.2 + 1)
  pure { newShape := newShape, newRoots := newRoots, newDiagonal := newDiagonal,
         tempV := tempV, tempO := tempO }

/-- the state of the loop copying the parts of the diagonal -/
structure SL where
  tempV : Mat
  tempO : Mat
  cx : Int
  cy : Int
  deriving Repr, DecidableEq

/-- the values computed in one iteration of `for (i in newShape.indices)` before
`copyOffset` -/
structure SPre where
  s : Int × Int
  tempV : Mat
  opart : Mat
  deriving Repr, DecidableEq

/-- one iteration of `for (i in newShape.indices)`, up to `offsetPart` -/
def shapePre (vm om : Mat) (p : Prep) (i : Nat) (st : SL) : R SPre := do
  let s ← aget p.newShape i
  let r ← aget p.newRoots i
  let vpart ← slice vm r.1 r.2 (r.1 + s.1) (r.2 + s.2)
  let vpart ← mset vpart 0 0 (← aget p.newDiagonal i)
  let tempV ← paste st.tempV vpart st.cx st.cy
  let opart ← slice om r.1 r.2 (r.1 + s.1) (r.2 + s.2)
  pure { s := s, tempV := tempV, opart := opart }

/-- `if (s.second > 0) offsetPart = offsetPart.copyOffset(offsetPart.badRoot, size = tempOffset.width)` -/
def shapeMid (fuel : Nat) (st : SL) (x : SPre) : R Mat :=
  if x.s.2 > 0 then do
    let b ← badRoot x.opart
    let tw ← width st.tempO
    copyOffset fuel x.opart b none (some tw)
  else pure x.opart

/-- the rest of one iteration of `for (i in newShape.indices)` -/
def shapePost (st : SL) (x : SPre) (opart : Mat) : R SL := do
  let tempO ← paste st.tempO opart st.cx st.cy
  pure { tempV := x.tempV, tempO := tempO, cx := st.cx + x.s.1, cy := st.cy + x.s.2 }

/-- one iteration of `for (i in newShape.indices)` -/
def shapeStep (fuel : Nat) (vm om : Mat) (p : Prep) (i : Nat) (st : SL) : R SL := do
  let x ← shapePre vm om p i st
  let o ← shapeMid fuel st x
  shapePost st x o

/-- `for (i in newShape.indices)` -/
def shapeLoop (fuel : Nat) (vm om : Mat) (p : Prep) : List Nat → SL → R SL
  | [], st => pure st
  | i :: is, st => do shapeLoop fuel vm om p is (← shapeStep fuel vm om p i st)

/-- the end of the diagonal expansion -/
def diagEnd (p : Prep) (st : SL) (br : Int) : R Exp := do
  let tempV ← mset st.tempV st.cy st.cx (← aget p.newDiagonal p.newShape.length)
  let v ← refill tempV st.tempO
  pure { vm := v, om := st.tempO, br := br }

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
  let om ← copyOffset fuel om br (some times) none
  normalRest vm om br times

/-- `lastRow.last() > 1` where `lastRow = valueMat.last()` -/
def isDiag (mt : Mtn) : R Bool := do
  let lastRow ← last mt.vm
  pure (decide ((← last lastRow) > 1))

/-- the initial state of `for (i in newShape.indices)` -/
def initSL (p : Prep) : SL := { tempV := p.tempV, tempO := p.tempO, cx := 0, cy := 0 }

/-- `expand(seq, times)` -/
def expand : Nat → Row → Int → R Exp
  | 0, _, _ => .div
  | f + 1, seq, times => do
    let mt ← mountain (f + 1) seq
    let br ← badRoot mt.om
    if ← isDiag mt then
      let w ← walk (f + 1) mt.vm mt.om
      let shape ← removeLast w.shape
      let ed ← expand f w.diagonal (times + 2)
      let p ← diagPrep mt.vm mt.om shape ed times
      let st ← shapeLoop (f + 1) mt.vm mt.om p (List.range p.newShape.length) (initSL p)
      diagEnd p st br
    else
      normal (f + 1) mt.vm mt.om br times

/-- `main`: the output for the input `(seq)[times]` -/
def main (fuel : Nat) (seq : Row) (times : Int) : R (Row × Int) := do
  if (← last seq) == 1 then pure (seq.dropLast, times + 1)
  else do
    let e ← expand fuel seq times
    pure (← aget e.vm 0, times)

end Bismuth
