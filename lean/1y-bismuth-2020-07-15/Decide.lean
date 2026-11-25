import «1y-bismuth-2020-07-15».Model
import «1y-bismuth».Decide

/-!
# A decision procedure for non-termination (version of 2020-07-15)

`mainD` runs the same program as `main`, except for the parts that use the step
budget:

* the `while` loops computing the differences and the `do … while` loops
  computing `forcedOffset` run with a fixed bound (`bound` if it is exceeded,
  which gives no information);
* the `while` loop of `copyOffset` stops with `stuck` as soon as its body can no
  longer write anything (`copyWidth ≤ 0`, or every `target` is `≥ newWidth`)
  while the loop condition still holds;
* the recursion of `expand` has a fixed depth bound.

The generic parts (`RD`, `lift`, `Approx`, `whileD`, `coIdle`) are those of the
version of 2019-09-29.  `main_div_of_stuck` shows that if `mainD` returns
`stuck`, then `main` returns `div` for every `fuel`, i.e. the program runs
forever.
-/

namespace Bismuth2020

open Bismuth (R Row Mat RD lift Approx approx_lift approx_pure approx_bind approx_bind_lift
  div_of_stuck whileD approx_whileD whileF coIdle coIdle_succ bnd aget width resize badRoot
  removeLast first last)

/-! ## the loop of `copyOffset` -/

theorem copyBlock_idle (res : Mat) (br copyW newW i : Int) (h : coIdle br copyW newW i) :
    copyBlock res br copyW newW i = .ok res := by
  unfold copyBlock
  by_cases hc : copyW ≤ 0
  · have : copyW.toNat = 0 := by omega
    rw [this]
    rfl
  · have h' : newW ≤ br + copyW * i + 1 := by
      rcases h with h | h
      · exact absurd h hc
      · exact h
    obtain ⟨n, hn⟩ : ∃ n, copyW.toNat = n + 1 := ⟨copyW.toNat - 1, by omega⟩
    rw [hn, List.range_succ_eq_map]
    simp only [copyBlockAux]
    rw [if_pos (by omega)]
    rfl

/-- the `while` loop of `copyOffset` never ends once its body is idle -/
theorem whileF_co_div (br copyW newW : Int) (res : Mat) (hc : coCond (res, 0) = .ok true) :
    ∀ (f : Nat) (i : Int), coIdle br copyW newW i →
      whileF coCond (coBody br copyW newW) f (res, i) = .div := by
  have hc' : ∀ i, coCond (res, i) = .ok true := fun _ => hc
  have hb : ∀ i, coIdle br copyW newW i → coBody br copyW newW (res, i) = .ok (res, i + 1) := by
    intro i hi
    simp only [coBody, copyBlock_idle res br copyW newW i hi]
    rfl
  intro f
  induction f with
  | zero =>
    intro i _
    simp only [whileF, hc' i]
    rfl
  | succ f ih =>
    intro i hi
    simp only [whileF, hc' i]
    show (do whileF coCond (coBody br copyW newW) f (← coBody br copyW newW (res, i))) = _
    rw [hb i hi]
    exact ih (i + 1) (coIdle_succ hi)

/-- the `while` loop of `copyOffset` with a fixed bound, stopping with `stuck` -/
def copyLoopD (br copyW newW : Int) : Nat → Mat × Int → RD (Mat × Int)
  | 0, _ => .bound
  | b + 1, st => do
    if ← lift (coCond st) then
      if coIdle br copyW newW st.2 then .stuck
      else copyLoopD br copyW newW b (← lift (coBody br copyW newW st))
    else pure st

theorem approx_copyLoopD (br copyW newW : Int) :
    ∀ (b f : Nat) (st : Mat × Int),
      Approx (copyLoopD br copyW newW b st) (whileF coCond (coBody br copyW newW) f st)
  | 0, _, _ => Or.inr trivial
  | b + 1, f, st => by
    obtain ⟨res, i⟩ := st
    simp only [copyLoopD]
    have hw : whileF coCond (coBody br copyW newW) f (res, i) =
        (coCond (res, i) >>= fun c =>
          if c then (match f with
            | 0 => .div
            | f + 1 => coBody br copyW newW (res, i) >>= whileF coCond (coBody br copyW newW) f)
          else pure (res, i)) := by
      cases f <;> rfl
    rw [hw]
    refine approx_bind_lift _ fun c hc => ?_
    cases c
    · exact approx_pure _
    · simp only [if_true]
      by_cases hi : coIdle br copyW newW i
      · rw [if_pos hi]
        have h0 : coCond (res, 0) = .ok true := hc
        cases f with
        | zero => exact Or.inl rfl
        | succ f =>
          left
          have hb : coBody br copyW newW (res, i) = .ok (res, i + 1) := by
            simp only [coBody, copyBlock_idle res br copyW newW i hi]
            rfl
          show (do whileF coCond (coBody br copyW newW) f (← coBody br copyW newW (res, i))) = _
          rw [hb]
          exact whileF_co_div br copyW newW res h0 f (i + 1) (coIdle_succ hi)
      · rw [if_neg hi]
        cases f with
        | zero => exact Or.inl rfl
        | succ f =>
          exact approx_bind_lift _ fun st' _ => approx_copyLoopD br copyW newW b f st'

/-- `copyOffset` of the decision procedure -/
def copyOffsetD (m : Mat) (br times : Int) : RD Mat := do
  let w ← lift (width m)
  let copyW := w - br - 1
  let newW := br + copyW * times + 1
  let res ← lift (resize m newW m.length)
  let st ← copyLoopD br copyW newW bnd (res, 1)
  pure st.1

theorem approx_copyOffsetD (f : Nat) (m : Mat) (br times : Int) :
    Approx (copyOffsetD m br times) (copyOffset f m br times) := by
  simp only [copyOffsetD, copyOffset]
  refine approx_bind_lift _ fun w _ => ?_
  refine approx_bind_lift _ fun res _ => ?_
  exact approx_bind (approx_copyLoopD _ _ _ bnd f _) fun st _ => approx_pure _

/-! ## the stages of `expand` -/

def mountainD (seq : Row) (fo : Option Row) : RD Mtn :=
  whileD mtnCond (mtnBody fo) bnd { vm := [seq], om := [List.replicate seq.length 0], row := 0 }

theorem approx_mountainD (f : Nat) (seq : Row) (fo : Option Row) :
    Approx (mountainD seq fo) (mountain f seq fo) :=
  approx_whileD _ _ bnd f _

def forcedAtD (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row) (i : Nat) : RD Int := do
  let r ← lift (aget roots i)
  let di ← lift (aget diagonal i)
  let st ← lift (foBody vm om { c := r, done := false })
  let st ← whileD (foCond vm di) (foBody vm om) bnd st
  pure (foResult roots i di st)

theorem approx_forcedAtD (f : Nat) (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row)
    (i : Nat) : Approx (forcedAtD vm om roots diagonal i) (forcedAt f vm om roots diagonal i) := by
  simp only [forcedAtD, forcedAt]
  refine approx_bind_lift _ fun r _ => ?_
  refine approx_bind_lift _ fun di _ => ?_
  refine approx_bind_lift _ fun st _ => ?_
  exact approx_bind (approx_whileD _ _ bnd f _) fun st' _ => approx_pure _

def forcedListD (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row) :
    List Nat → RD (List Int)
  | [] => pure []
  | i :: is => do
    let a ← forcedAtD vm om roots diagonal i
    let as ← forcedListD vm om roots diagonal is
    pure (a :: as)

theorem approx_forcedListD (f : Nat) (vm om : Mat) (roots : List (Int × Int)) (diagonal : Row) :
    ∀ l : List Nat,
      Approx (forcedListD vm om roots diagonal l) (forcedList f vm om roots diagonal l)
  | [] => approx_pure _
  | i :: is =>
    approx_bind (approx_forcedAtD f vm om roots diagonal i) fun _ _ =>
      approx_bind (approx_forcedListD f vm om roots diagonal is) fun _ _ => approx_pure _

def diagPrepD (vm om : Mat) (shape : List Int) (roots : List (Int × Int)) (ed : Exp)
    (times : Int) : RD Prep := do
  let x ← lift (diagPre om vm shape roots ed times)
  let badPart ← copyOffsetD x.bp 0 times
  lift (diagPost vm om x badPart)

theorem approx_diagPrepD (f : Nat) (vm om : Mat) (shape : List Int) (roots : List (Int × Int))
    (ed : Exp) (times : Int) :
    Approx (diagPrepD vm om shape roots ed times) (diagPrep f vm om shape roots ed times) := by
  unfold diagPrepD diagPrep
  refine approx_bind_lift _ fun x _ => ?_
  exact approx_bind (approx_copyOffsetD f _ _ _) fun _ _ => approx_lift _

def shapeMidD (p : Prep) (times : Int) (st : SL) (x : SPre) : RD Mat :=
  if st.row ≥ p.badY ∧ x.s > 0 then lift (shapeBad p st x)
  else if x.s > 0 then copyOffsetD x.opart (p.badX - x.i) times
  else pure x.opart

theorem approx_shapeMidD (f : Nat) (p : Prep) (times : Int) (st : SL) (x : SPre) :
    Approx (shapeMidD p times st x) (shapeMid f p times st x) := by
  unfold shapeMidD shapeMid
  by_cases h1 : st.row ≥ p.badY ∧ x.s > 0
  · rw [if_pos h1, if_pos h1]
    exact approx_lift _
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : x.s > 0
    · rw [if_pos h2, if_pos h2]
      exact approx_copyOffsetD f _ _ _
    · rw [if_neg h2, if_neg h2]
      exact approx_pure _

def shapeStepD (p : Prep) (times : Int) (i : Nat) (st : SL) : RD SL := do
  let x ← lift (shapePre p i st)
  let o ← shapeMidD p times st x
  lift (shapePost p st x o)

theorem approx_shapeStepD (f : Nat) (p : Prep) (times : Int) (i : Nat) (st : SL) :
    Approx (shapeStepD p times i st) (shapeStep f p times i st) := by
  unfold shapeStepD shapeStep
  refine approx_bind_lift _ fun x _ => ?_
  exact approx_bind (approx_shapeMidD f p times st x) fun _ _ => approx_lift _

def shapeLoopD (p : Prep) (times : Int) : List Nat → SL → RD SL
  | [], st => pure st
  | i :: is, st => do shapeLoopD p times is (← shapeStepD p times i st)

theorem approx_shapeLoopD (f : Nat) (p : Prep) (times : Int) :
    ∀ (l : List Nat) (st : SL), Approx (shapeLoopD p times l st) (shapeLoop f p times l st)
  | [], st => approx_pure st
  | i :: is, st =>
    approx_bind (approx_shapeStepD f p times i st) fun st' _ => approx_shapeLoopD f p times is st'

def normalD (vm om : Mat) (br times : Int) : RD Exp := do
  let om ← copyOffsetD om br times
  lift (normalRest vm om br times)

theorem approx_normalD (f : Nat) (vm om : Mat) (br times : Int) :
    Approx (normalD vm om br times) (normal f vm om br times) :=
  approx_bind (approx_copyOffsetD f _ _ _) fun _ _ => approx_lift _

/-- `expand` of the decision procedure, with recursion depth `d` -/
def expandD : Nat → Row → Int → Option Row → RD Exp
  | 0, _, _, _ => .bound
  | d + 1, seq, times, fo => do
    let mt ← mountainD seq fo
    let br ← lift (badRoot mt.om)
    if ← lift (isDiag mt) then
      let roots ← lift (rootsOf mt.vm)
      let diagonal ← lift (diagonalOf mt.vm roots)
      let shape := shapeOf roots
      let forced ← forcedListD mt.vm mt.om roots diagonal (List.range roots.length)
      let roots' ← lift (removeLast roots)
      let ed ← expandD d diagonal (times + 1) (some forced)
      let p ← diagPrepD mt.vm mt.om shape roots' ed times
      let st ← shapeLoopD p times (List.range p.newShape.length) (initSL mt.vm mt.om p)
      lift (diagEnd p st br)
    else
      normalD mt.vm mt.om br times

theorem approx_expandD : ∀ (d f : Nat) (seq : Row) (times : Int) (fo : Option Row),
    Approx (expandD d seq times fo) (expand f seq times fo)
  | 0, _, _, _, _ => Or.inr trivial
  | _ + 1, 0, _, _, _ => Or.inl rfl
  | d + 1, f + 1, seq, times, fo => by
    simp only [expandD, expand]
    refine approx_bind (approx_mountainD (f + 1) seq fo) fun mt _ => ?_
    refine approx_bind_lift _ fun br _ => ?_
    refine approx_bind_lift _ fun c _ => ?_
    cases c
    · exact approx_normalD _ _ _ _ _
    · refine approx_bind_lift _ fun roots _ => ?_
      refine approx_bind_lift _ fun diagonal _ => ?_
      refine approx_bind (approx_forcedListD (f + 1) _ _ _ _ _) fun forced _ => ?_
      refine approx_bind_lift _ fun roots' _ => ?_
      refine approx_bind (approx_expandD d f _ _ _) fun ed _ => ?_
      refine approx_bind (approx_diagPrepD (f + 1) _ _ _ _ _ _) fun p _ => ?_
      refine approx_bind (approx_shapeLoopD (f + 1) _ _ _ _) fun st _ => ?_
      exact approx_lift _

/-- `main` of the decision procedure -/
def mainD (d : Nat) (seq : Row) (n : Int) : RD (Row × Int) := do
  if (← lift (last seq)) == 1 then pure (seq.dropLast, n + 1)
  else do
    let e ← expandD d seq (n + 1) none
    pure (← lift (first e.vm), n)

theorem approx_mainD (d f : Nat) (seq : Row) (n : Int) :
    Approx (mainD d seq n) (main f seq n) := by
  simp only [mainD, main]
  refine approx_bind_lift _ fun l _ => ?_
  split
  · exact approx_pure _
  · refine approx_bind (approx_expandD d f _ _ _) fun e _ => ?_
    exact approx_bind_lift _ fun r _ => approx_pure _

/-- **the decision procedure is sound for non-termination**: if `mainD` says
`stuck`, the program runs forever on `(seq)[n]` -/
theorem main_div_of_stuck (d : Nat) (seq : Row) (n : Int)
    (h : mainD d seq n = .stuck) (f : Nat) : main f seq n = .div := by
  have := approx_mainD d f seq n
  rw [h] at this
  exact div_of_stuck this

end Bismuth2020
