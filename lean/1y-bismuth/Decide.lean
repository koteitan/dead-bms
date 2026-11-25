import «1y-bismuth».Model

/-!
# A decision procedure for non-termination

`mainD` runs the same program as `main`, except for the parts that use the step
budget:

* the `while` loops computing the differences and walking the diagonal run with
  a fixed bound (`bound` if it is exceeded, which gives no information);
* the `while` loop of `copyOffset` stops with `stuck` as soon as its body can no
  longer write anything (`copyWidth ≤ 0`, or every `target` is `≥ newWidth`)
  while the loop condition still holds;
* the recursion of `expand` has a fixed depth bound.

`approx_main` shows that `mainD` predicts every run of `main`: in particular,
if `mainD` returns `stuck`, then `main` returns `div` for every `fuel`, i.e. the
Kotlin program runs forever.
-/

namespace Bismuth

/-- the outcome of the decision procedure -/
inductive RD (α : Type) where
  | ok : α → RD α
  | err : RD α
  | unsup : RD α
  /-- the program is in a loop that never ends -/
  | stuck : RD α
  /-- a bound of the decision procedure was exceeded (no conclusion) -/
  | bound : RD α
  deriving Repr, DecidableEq

instance : Monad RD where
  pure := .ok
  bind m k := match m with
    | .ok a => k a
    | .err => .err
    | .unsup => .unsup
    | .stuck => .stuck
    | .bound => .bound

/-- a piece of the program that does not use the budget -/
def lift {α : Type} : R α → RD α
  | .ok a => .ok a
  | .err => .err
  | .unsup => .unsup
  | .div => .bound

/-- `d` predicts the run `r`: either `r` ran out of budget, or `r` is what `d`
says (`stuck` allows only running out of budget, `bound` allows anything) -/
def Approx {α : Type} (d : RD α) (r : R α) : Prop :=
  r = .div ∨ match d with
    | .ok a => r = .ok a
    | .err => r = .err
    | .unsup => r = .unsup
    | .stuck => False
    | .bound => True

theorem approx_lift {α : Type} (r : R α) : Approx (lift r) r := by
  cases r <;> simp [Approx, lift]

theorem approx_pure {α : Type} (a : α) : Approx (pure a : RD α) (pure a) := Or.inr rfl

theorem approx_bind {α β : Type} {d : RD α} {r : R α} {kd : α → RD β} {k : α → R β}
    (h : Approx d r) (hk : ∀ a, r = .ok a → Approx (kd a) (k a)) :
    Approx (d >>= kd) (r >>= k) := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · cases d with
    | ok a =>
      simp only at h; subst h
      exact hk a rfl
    | err => simp only at h; subst h; exact Or.inr rfl
    | unsup => simp only at h; subst h; exact Or.inr rfl
    | stuck => exact h.elim
    | bound => exact Or.inr trivial

theorem approx_bind_lift {α β : Type} (r : R α) {kd : α → RD β} {k : α → R β}
    (hk : ∀ a, r = .ok a → Approx (kd a) (k a)) : Approx (lift r >>= kd) (r >>= k) :=
  approx_bind (approx_lift r) hk

theorem div_of_stuck {α : Type} {r : R α} (h : Approx (.stuck : RD α) r) : r = .div := by
  rcases h with h | h
  · exact h
  · exact h.elim

/-! ## loops with a fixed bound -/

/-- `whileF` with a fixed bound -/
def whileD {σ : Type} (cond : σ → R Bool) (body : σ → R σ) : Nat → σ → RD σ
  | 0, _ => .bound
  | b + 1, s => do if ← lift (cond s) then whileD cond body b (← lift (body s)) else pure s

theorem approx_whileD {σ : Type} (cond : σ → R Bool) (body : σ → R σ) :
    ∀ (b f : Nat) (s : σ), Approx (whileD cond body b s) (whileF cond body f s)
  | 0, _, _ => Or.inr trivial
  | b + 1, 0, s => by
    simp only [whileD, whileF]
    refine approx_bind_lift _ fun c _ => ?_
    cases c
    · exact approx_pure _
    · exact Or.inl rfl
  | b + 1, f + 1, s => by
    simp only [whileD, whileF]
    refine approx_bind_lift _ fun c _ => ?_
    cases c
    · exact approx_pure _
    · exact approx_bind_lift _ fun s' _ => approx_whileD cond body b f s'

/-! ## the loop of `copyOffset` -/

/-- the body of the loop writes nothing in iteration `i`, nor in any later one -/
def coIdle (br copyW newW i : Int) : Prop := copyW ≤ 0 ∨ newW ≤ br + copyW * i + 1

instance (br copyW newW i : Int) : Decidable (coIdle br copyW newW i) := by
  unfold coIdle; infer_instance

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

theorem coIdle_succ {br copyW newW i : Int} (h : coIdle br copyW newW i) :
    coIdle br copyW newW (i + 1) := by
  rcases h with h | h
  · exact Or.inl h
  · by_cases hc : copyW ≤ 0
    · exact Or.inl hc
    · right
      have : copyW * (i + 1) = copyW * i + copyW := by rw [Int.mul_add, Int.mul_one]
      rw [this]
      omega

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

/-- the bound used for every loop of the decision procedure -/
def bnd : Nat := 100000

/-- `copyOffset` of the decision procedure -/
def copyOffsetD (m : Mat) (br : Int) (times size : Option Int) : RD Mat := do
  let w ← lift (width m)
  let copyW := w - br - 1
  let newW ← lift (coNewW br copyW times size)
  let res ← lift (resize m newW m.length)
  let st ← copyLoopD br copyW newW bnd (res, 1)
  pure st.1

theorem approx_copyOffsetD (f : Nat) (m : Mat) (br : Int) (times size : Option Int) :
    Approx (copyOffsetD m br times size) (copyOffset f m br times size) := by
  simp only [copyOffsetD, copyOffset]
  refine approx_bind_lift _ fun w _ => ?_
  refine approx_bind_lift _ fun newW _ => ?_
  refine approx_bind_lift _ fun res _ => ?_
  exact approx_bind (approx_copyLoopD _ _ _ bnd f _) fun st _ => approx_pure _

/-! ## the stages of `expand` -/

def mountainD (seq : Row) : RD Mtn :=
  whileD mtnCond mtnBody bnd { vm := [seq], om := [List.replicate seq.length 0], row := 0 }

theorem approx_mountainD (f : Nat) (seq : Row) : Approx (mountainD seq) (mountain f seq) :=
  approx_whileD _ _ bnd f _

def walkD (vm om : Mat) : RD Walk :=
  whileD (walkCond vm) (walkBody vm om) bnd { shape := [], diagonal := [], cx := 0, cy := 0 }

theorem approx_walkD (f : Nat) (vm om : Mat) : Approx (walkD vm om) (walk f vm om) :=
  approx_whileD _ _ bnd f _

def shapeMidD (st : SL) (x : SPre) : RD Mat :=
  if x.s.2 > 0 then do
    let b ← lift (badRoot x.opart)
    let tw ← lift (width st.tempO)
    copyOffsetD x.opart b none (some tw)
  else pure x.opart

theorem approx_shapeMidD (f : Nat) (st : SL) (x : SPre) :
    Approx (shapeMidD st x) (shapeMid f st x) := by
  unfold shapeMidD shapeMid
  split
  · refine approx_bind_lift _ fun b _ => ?_
    refine approx_bind_lift _ fun tw _ => ?_
    exact approx_copyOffsetD f _ _ _ _
  · exact approx_pure _

def shapeStepD (vm om : Mat) (p : Prep) (i : Nat) (st : SL) : RD SL := do
  let x ← lift (shapePre vm om p i st)
  let o ← shapeMidD st x
  lift (shapePost st x o)

theorem approx_shapeStepD (f : Nat) (vm om : Mat) (p : Prep) (i : Nat) (st : SL) :
    Approx (shapeStepD vm om p i st) (shapeStep f vm om p i st) := by
  unfold shapeStepD shapeStep
  refine approx_bind_lift _ fun x _ => ?_
  exact approx_bind (approx_shapeMidD f st x) fun o _ => approx_lift _

def shapeLoopD (vm om : Mat) (p : Prep) : List Nat → SL → RD SL
  | [], st => pure st
  | i :: is, st => do shapeLoopD vm om p is (← shapeStepD vm om p i st)

theorem approx_shapeLoopD (f : Nat) (vm om : Mat) (p : Prep) :
    ∀ (l : List Nat) (st : SL), Approx (shapeLoopD vm om p l st) (shapeLoop f vm om p l st)
  | [], st => approx_pure st
  | i :: is, st =>
    approx_bind (approx_shapeStepD f vm om p i st) fun st' _ => approx_shapeLoopD f vm om p is st'

def normalD (vm om : Mat) (br times : Int) : RD Exp := do
  let om ← copyOffsetD om br (some times) none
  lift (normalRest vm om br times)

theorem approx_normalD (f : Nat) (vm om : Mat) (br times : Int) :
    Approx (normalD vm om br times) (normal f vm om br times) :=
  approx_bind (approx_copyOffsetD f _ _ _ _) fun _ _ => approx_lift _

/-- `expand` of the decision procedure, with recursion depth `d` -/
def expandD : Nat → Row → Int → RD Exp
  | 0, _, _ => .bound
  | d + 1, seq, times => do
    let mt ← mountainD seq
    let br ← lift (badRoot mt.om)
    if ← lift (isDiag mt) then
      let w ← walkD mt.vm mt.om
      let shape ← lift (removeLast w.shape)
      let ed ← expandD d w.diagonal (times + 2)
      let p ← lift (diagPrep mt.vm mt.om shape ed times)
      let st ← shapeLoopD mt.vm mt.om p (List.range p.newShape.length) (initSL p)
      lift (diagEnd p st br)
    else
      normalD mt.vm mt.om br times

theorem approx_expandD : ∀ (d f : Nat) (seq : Row) (times : Int),
    Approx (expandD d seq times) (expand f seq times)
  | 0, _, _, _ => Or.inr trivial
  | _ + 1, 0, _, _ => Or.inl rfl
  | d + 1, f + 1, seq, times => by
    simp only [expandD, expand]
    refine approx_bind (approx_mountainD (f + 1) seq) fun mt _ => ?_
    refine approx_bind_lift _ fun br _ => ?_
    refine approx_bind_lift _ fun c _ => ?_
    cases c
    · exact approx_normalD _ _ _ _ _
    · refine approx_bind (approx_walkD (f + 1) _ _) fun w _ => ?_
      refine approx_bind_lift _ fun shape _ => ?_
      refine approx_bind (approx_expandD d f _ _) fun ed _ => ?_
      refine approx_bind_lift _ fun p _ => ?_
      refine approx_bind (approx_shapeLoopD (f + 1) _ _ _ _ _) fun st _ => ?_
      exact approx_lift _

/-- `main` of the decision procedure -/
def mainD (d : Nat) (seq : Row) (times : Int) : RD (Row × Int) := do
  if (← lift (last seq)) == 1 then pure (seq.dropLast, times + 1)
  else do
    let e ← expandD d seq times
    pure (← lift (aget e.vm 0), times)

theorem approx_mainD (d f : Nat) (seq : Row) (times : Int) :
    Approx (mainD d seq times) (main f seq times) := by
  simp only [mainD, main]
  refine approx_bind_lift _ fun l _ => ?_
  split
  · exact approx_pure _
  · refine approx_bind (approx_expandD d f _ _) fun e _ => ?_
    exact approx_bind_lift _ fun r _ => approx_pure _

/-- **the decision procedure is sound for non-termination**: if `mainD` says
`stuck`, the Kotlin program runs forever on `(seq)[times]` -/
theorem main_div_of_stuck (d : Nat) (seq : Row) (times : Int)
    (h : mainD d seq times = .stuck) (f : Nat) : main f seq times = .div := by
  have := approx_mainD d f seq times
  rw [h] at this
  exact div_of_stuck this

end Bismuth
