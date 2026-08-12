import Principia.Syntax.Apparent

namespace PM.CanonicalOrderedFormula

/-! Canonical, order-unbounded syntax for the binder-sensitive ✱9 reductions.
It is syntax only: it carries neither assertions nor inference rules. -/

inductive Quantifier where
  | always | sometimes
  deriving DecidableEq, Repr

inductive Raw : RealContext → Type where
  | elementary : Elementary Γ → Raw Γ
  | bound : Nat → Raw Γ
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

def openOuterAt (cutoff : Nat) : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary p => .elementary
      (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  | .bound index =>
      if index < cutoff + 1 then .bound index
      else if index = cutoff + 1 then .elementary (.var .zero)
      else .bound (index - 1)
  | .quantified q body => .quantified q (openOuterAt (cutoff + 1) body)
  | .neg p => .neg (openOuterAt cutoff p)
  | .disj p q => .disj (openOuterAt cutoff p) (openOuterAt cutoff q)

def openOuter (p : Raw Γ) : Raw (.elementaryProposition :: Γ) :=
  openOuterAt 0 p

/-- Reify an elementary formula over a leading real variable as Raw syntax
under one additional outer binder. -/
def abstractElementary : Elementary (.elementaryProposition :: Γ) → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var .zero => .bound 1
  | .var (.succ v) => .elementary (.var v)
  | .neg p => .neg (abstractElementary p)
  | .disj p q => .disj (abstractElementary p) (abstractElementary q)

def abstractElementaryAt (cutoff : Nat) :
    Elementary (.elementaryProposition :: Γ) → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var .zero => .bound (cutoff + 1)
  | .var (.succ v) => .elementary (.var v)
  | .neg p => .neg (abstractElementaryAt cutoff p)
  | .disj p q => .disj (abstractElementaryAt cutoff p) (abstractElementaryAt cutoff q)

def abstractOuterAt (cutoff : Nat) : Raw (.elementaryProposition :: Γ) → Raw Γ
  | .elementary p => abstractElementaryAt cutoff p
  | .bound index =>
      if index ≤ cutoff then .bound index else .bound (index + 1)
  | .quantified q body => .quantified q (abstractOuterAt (cutoff + 1) body)
  | .neg p => .neg (abstractOuterAt cutoff p)
  | .disj p q => .disj (abstractOuterAt cutoff p) (abstractOuterAt cutoff q)

def abstractOuter (p : Raw (.elementaryProposition :: Γ)) : Raw Γ :=
  abstractOuterAt 0 p

/-- Raw terms admissible for an outer real abstraction at a given binder
depth.  The reserved index `cutoff + 1` is excluded because it is introduced
only by `abstractOuterAt`; this is the exact image invariant for its beta law. -/
def Admissible (cutoff : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .bound index => index ≠ cutoff + 1
  | .quantified _ body => Admissible (cutoff + 1) body
  | .neg p => Admissible cutoff p
  | .disj p q => Admissible cutoff p ∧ Admissible cutoff q

def shiftIndex (cutoff index : Nat) : Nat :=
  if cutoff ≤ index then index + 1 else index

/-- The elementary de Bruijn arithmetic underlying capture-safe shift
commutation.  Inserting at `i` first moves the later insertion point `j` to
`j + 1`. -/
theorem shiftIndex_comm (i j index : Nat) (h : i ≤ j) :
    shiftIndex (j + 1) (shiftIndex i index) =
      shiftIndex i (shiftIndex j index) := by
  by_cases hi : i ≤ index
  · by_cases hj : j ≤ index
    · have hleft : j + 1 ≤ index + 1 := by omega
      have hright : i ≤ index + 1 := by omega
      simp [shiftIndex, hi, hj, hleft, hright]
    · have hleft : ¬ j + 1 ≤ index + 1 := by omega
      simp [shiftIndex, hi, hj, hleft]
  · have hj : ¬ j ≤ index := by omega
    have hleft : ¬ j + 1 ≤ index := by omega
    simp [shiftIndex, hi, hj, hleft]

def shiftBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => .bound (shiftIndex cutoff index)
  | .quantified q body => .quantified q (shiftBoundAt (cutoff + 1) body)
  | .neg p => .neg (shiftBoundAt cutoff p)
  | .disj p q => .disj (shiftBoundAt cutoff p) (shiftBoundAt cutoff q)

def weakenBound (p : Raw Γ) : Raw Γ := shiftBoundAt 0 p

/-- Capture-safe shifts commute when the later insertion point is adjusted
after the first insertion. -/
theorem shiftBoundAt_comm (i j : Nat) (p : Raw Γ) (h : i ≤ j) :
    shiftBoundAt (j + 1) (shiftBoundAt i p) =
      shiftBoundAt i (shiftBoundAt j p) := by
  induction p generalizing i j with
  | elementary proposition => rfl
  | bound index => exact congrArg Raw.bound (shiftIndex_comm i j index h)
  | quantified quantifier body ih =>
      simp only [shiftBoundAt]
      exact congrArg (Raw.quantified quantifier) (ih (i + 1) (j + 1) (by omega))
  | neg proposition ih =>
      simp only [shiftBoundAt]
      exact congrArg Raw.neg (ih i j h)
  | disj left right ihLeft ihRight =>
      simp only [shiftBoundAt]
      rw [ihLeft i j h, ihRight i j h]

/-- `FreshBelowAt depth count` records the binder-sensitive freshness
invariant for `count` outer lifts: local binders below `depth` remain valid,
whereas every external index lies at or beyond `depth + count`. -/
def FreshBelowAt (depth count : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .bound index => index < depth ∨ depth + count ≤ index
  | .quantified _ body => FreshBelowAt (depth + 1) count body
  | .neg p => FreshBelowAt depth count p
  | .disj p q => FreshBelowAt depth count p ∧ FreshBelowAt depth count q

def FreshBelow (count : Nat) (p : Raw Γ) : Prop := FreshBelowAt 0 count p

theorem freshBelowAt_zero (depth : Nat) (p : Raw Γ) : FreshBelowAt depth 0 p := by
  induction p generalizing depth with
  | elementary proposition => trivial
  | bound index =>
      by_cases below : index < depth
      · exact Or.inl below
      · exact Or.inr (by omega)
  | quantified quantifier body ih => exact ih (depth + 1)
  | neg proposition ih => exact ih depth
  | disj left right ihLeft ihRight => exact ⟨ihLeft depth, ihRight depth⟩

theorem freshBelowAt_shift (depth count : Nat) (p : Raw Γ) :
    FreshBelowAt depth count p →
      FreshBelowAt depth (count + 1) (shiftBoundAt depth p) := by
  intro fresh
  induction p generalizing depth count with
  | elementary proposition => trivial
  | bound index =>
      simp only [FreshBelowAt, shiftBoundAt]
      rcases fresh with inner | external
      · have noShift : ¬ depth ≤ index := by omega
        simp [shiftIndex, noShift]
        exact Or.inl inner
      · have doShift : depth ≤ index := by omega
        simp [shiftIndex, doShift]
        exact Or.inr (by omega)
  | quantified quantifier body ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ih (depth + 1) count fresh
  | neg proposition ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ih depth count fresh
  | disj left right ihLeft ihRight =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ⟨ihLeft depth count fresh.1, ihRight depth count fresh.2⟩

/-- A Raw term does not use the binder located at `cutoff`.  This is the
precise side condition needed to remove that binder without capture. -/
def UnusedBoundAt (cutoff : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .bound index => index ≠ cutoff
  | .quantified _ body => UnusedBoundAt (cutoff + 1) body
  | .neg p => UnusedBoundAt cutoff p
  | .disj p q => UnusedBoundAt cutoff p ∧ UnusedBoundAt cutoff q

/-- Remove an unused binder at `cutoff`.  Bound indices above the removed
slot are lowered; terms satisfying `UnusedBoundAt` never take the fallback
zero case at that slot. -/
def dropUnusedBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index =>
      if index < cutoff then .bound index else .bound (index - 1)
  | .quantified q body => .quantified q (dropUnusedBoundAt (cutoff + 1) body)
  | .neg p => .neg (dropUnusedBoundAt cutoff p)
  | .disj p q => .disj (dropUnusedBoundAt cutoff p) (dropUnusedBoundAt cutoff q)

def dropUnusedBound (p : Raw Γ) : Raw Γ := dropUnusedBoundAt 0 p

theorem shiftBoundAt_dropUnusedBoundAt
    (p : Raw Γ) (h : UnusedBoundAt cutoff p) :
    shiftBoundAt cutoff (dropUnusedBoundAt cutoff p) = p := by
  induction p generalizing cutoff with
  | elementary proposition => rfl
  | bound index =>
      simp only [UnusedBoundAt] at h
      by_cases below : index < cutoff
      · have noShift : ¬ cutoff ≤ index := by omega
        simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, below, noShift]
      · have above : cutoff < index := by omega
        have shifted : cutoff ≤ index - 1 := by omega
        simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, below, shifted]
        omega
  | quantified quantifier body ih =>
      simp only [dropUnusedBoundAt, shiftBoundAt]
      exact congrArg (Raw.quantified quantifier) (ih h)
  | neg proposition ih =>
      simp only [dropUnusedBoundAt, shiftBoundAt]
      exact congrArg Raw.neg (ih h)
  | disj left right ihLeft ihRight =>
      simp only [dropUnusedBoundAt, shiftBoundAt] at h ⊢
      rw [ihLeft h.1, ihRight h.2]

theorem weakenBound_dropUnusedBound
    (p : Raw Γ) (h : UnusedBoundAt 0 p) :
    weakenBound (dropUnusedBound p) = p :=
  shiftBoundAt_dropUnusedBoundAt p h

/-- Capture-safe renaming of apparent binder indices.  Under a quantifier the
newly bound index remains zero and every older index is renamed through the
lifted map. -/
def renameBound (ρ : Nat → Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => .bound (ρ index)
  | .quantified q body =>
      .quantified q (renameBound (fun index =>
        match index with | 0 => 0 | n + 1 => ρ n + 1) body)
  | .neg p => .neg (renameBound ρ p)
  | .disj p q => .disj (renameBound ρ p) (renameBound ρ q)

/-- A capture-safe replacement of elementary leaves by canonical Raw syntax.
When crossing an apparent binder, every replacement is weakened explicitly;
bound indices themselves remain bound indices. -/
abbrev Substitution (Γ Ξ : RealContext) := Elementary Γ → Raw Ξ

namespace Substitution

/-- Lift a Raw substitution through one apparent binder. -/
def lift (σ : Substitution Γ Ξ) : Substitution Γ Ξ :=
  fun proposition => weakenBound (σ proposition)

def liftN : Nat → Substitution Γ Ξ → Substitution Γ Ξ
  | 0, σ => σ
  | n + 1, σ => lift (liftN n σ)

@[simp] theorem lift_apply (σ : Substitution Γ Ξ) (proposition : Elementary Γ) :
    lift σ proposition = weakenBound (σ proposition) := rfl

@[simp] theorem liftN_zero (σ : Substitution Γ Ξ) : liftN 0 σ = σ := rfl

@[simp] theorem liftN_succ (n : Nat) (σ : Substitution Γ Ξ) :
    liftN (n + 1) σ = lift (liftN n σ) := rfl

end Substitution

def substitute (σ : Substitution Γ Ξ) : Raw Γ → Raw Ξ
  | .elementary proposition => σ proposition
  | .bound index => .bound index
  | .quantified quantifier body =>
      .quantified quantifier (substitute (Substitution.lift σ) body)
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

@[simp] theorem substitute_elementary (σ : Substitution Γ Ξ)
    (proposition : Elementary Γ) :
    substitute σ (.elementary proposition) = σ proposition := rfl

@[simp] theorem substitute_bound (σ : Substitution Γ Ξ) (index : Nat) :
    substitute σ (.bound index) = .bound index := rfl

theorem substitution_liftN_fresh (σ : Substitution Γ Ξ)
    (count : Nat) (proposition : Elementary Γ) :
    FreshBelow count (Substitution.liftN count σ proposition) := by
  induction count with
  | zero => exact freshBelowAt_zero 0 _
  | succ count ih =>
      change FreshBelowAt 0 (count + 1)
        (shiftBoundAt 0 (Substitution.liftN count σ proposition))
      exact freshBelowAt_shift 0 count _ ih

def smartNeg : Raw Γ → Raw Γ
  | .quantified .always body => .quantified .sometimes (smartNeg body)
  | .quantified .sometimes body => .quantified .always (smartNeg body)
  | proposition => .neg proposition

def rawSize : Raw Γ → Nat
  | .elementary _ | .bound _ => 1
  | .quantified _ p | .neg p => rawSize p + 1
  | .disj p q => rawSize p + rawSize q + 1

def smartDisjAux : Nat → Raw Γ → Raw Γ → Raw Γ
  | 0, p, q => .disj p q
  | fuel + 1, .quantified .always p, .quantified .sometimes q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified .sometimes p, .quantified .always q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified q p, r =>
      .quantified q (smartDisjAux fuel p (weakenBound r))
  | fuel + 1, p, .quantified q r =>
      .quantified q (smartDisjAux fuel (weakenBound p) r)
  | _ + 1, p, q => .disj p q

def smartDisj (p q : Raw Γ) : Raw Γ :=
  smartDisjAux (rawSize p + rawSize q) p q

def smartImp (p q : Raw Γ) : Raw Γ := smartDisj (smartNeg p) q

@[simp] theorem shiftBoundAt_elementary (p : Elementary Γ) :
    shiftBoundAt cutoff (.elementary p) = .elementary p := rfl

@[simp] theorem smartNeg_always (p : Raw Γ) :
    smartNeg (.quantified .always p) = .quantified .sometimes (smartNeg p) := rfl

end PM.CanonicalOrderedFormula
