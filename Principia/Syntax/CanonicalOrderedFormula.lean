import Principia.Syntax.Apparent

namespace PM.CanonicalOrderedFormula

/-! Canonical, order-unbounded syntax for the binder-sensitive ✱9 reductions.
It is syntax only: it carries neither assertions nor inference rules. -/

inductive Quantifier where
  | always | sometimes
  deriving DecidableEq, Repr

inductive Raw : RealContext → Type where
  | elementary : Elementary Γ → Raw Γ
  /-- Dedicated theorem-schema placeholder, distinct from an elementary PM
  formula and therefore never acted on by elementary schema instantiation. -/
  | schema : Nat → Raw Γ
  | bound : Nat → Raw Γ
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

def openOuterAt (cutoff : Nat) : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary p => .elementary
      (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  | .schema slot => .schema slot
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
  | .schema slot => .schema slot
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
  | .schema _ => True
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
  | .schema slot => .schema slot
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
  | schema slot => rfl
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

/-- Two successive outer lifts equal the scope-aware shift of the first
lifted term at cutoff one. -/
theorem weakenBound_weakenBound_eq_shiftBoundAt_one (p : Raw Γ) :
    weakenBound (weakenBound p) = shiftBoundAt 1 (weakenBound p) := by
  simpa [weakenBound] using (shiftBoundAt_comm 0 0 p (by omega)).symm

/-- `FreshBelowAt depth count` records the binder-sensitive freshness
invariant for `count` outer lifts: local binders below `depth` remain valid,
whereas every external index lies at or beyond `depth + count`. -/
def FreshBelowAt (depth count : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .schema _ => True
  | .bound index => index < depth ∨ depth + count ≤ index
  | .quantified _ body => FreshBelowAt (depth + 1) count body
  | .neg p => FreshBelowAt depth count p
  | .disj p q => FreshBelowAt depth count p ∧ FreshBelowAt depth count q

def FreshBelow (count : Nat) (p : Raw Γ) : Prop := FreshBelowAt 0 count p

theorem freshBelowAt_zero (depth : Nat) (p : Raw Γ) : FreshBelowAt depth 0 p := by
  induction p generalizing depth with
  | elementary proposition => trivial
  | schema slot => trivial
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
  | schema slot => trivial
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

/-- On a term fresh for `count` external binders, shifting at the external
cutoff `depth + count` is the same operation as lifting at the local cutoff
`depth`. -/
theorem shiftBoundAt_freshBelowAt (depth count : Nat) (p : Raw Γ)
    (fresh : FreshBelowAt depth count p) :
    shiftBoundAt (depth + count) p = shiftBoundAt depth p := by
  induction p generalizing depth count with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index =>
      simp only [FreshBelowAt] at fresh
      simp only [shiftBoundAt]
      rcases fresh with inner | external
      · have leftNo : ¬ depth + count ≤ index := by omega
        have rightNo : ¬ depth ≤ index := by omega
        simp [shiftIndex, leftNo, rightNo]
      · have leftYes : depth + count ≤ index := external
        have rightYes : depth ≤ index := by omega
        simp [shiftIndex, leftYes, rightYes]
  | quantified quantifier body ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      congr 1
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (depth + 1) count fresh
  | neg proposition ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact congrArg Raw.neg (ih depth count fresh)
  | disj left right ihLeft ihRight =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      rw [ihLeft depth count fresh.1, ihRight depth count fresh.2]

/-- A Raw term does not use the binder located at `cutoff`.  This is the
precise side condition needed to remove that binder without capture. -/
def UnusedBoundAt (cutoff : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .schema _ => True
  | .bound index => index ≠ cutoff
  | .quantified _ body => UnusedBoundAt (cutoff + 1) body
  | .neg p => UnusedBoundAt cutoff p
  | .disj p q => UnusedBoundAt cutoff p ∧ UnusedBoundAt cutoff q

/-- Remove an unused binder at `cutoff`.  Bound indices above the removed
slot are lowered; terms satisfying `UnusedBoundAt` never take the fallback
zero case at that slot. -/
def dropUnusedBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .schema slot => .schema slot
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
  | schema slot => rfl
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
  | .schema slot => .schema slot
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
  | .schema slot => .schema slot
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

theorem substitution_liftN_succ_as_shift (σ : Substitution Γ Ξ)
    (count : Nat) (proposition : Elementary Γ) :
    Substitution.liftN (count + 1) σ proposition =
      shiftBoundAt count (Substitution.liftN count σ proposition) := by
  change shiftBoundAt 0 (Substitution.liftN count σ proposition) = _
  simpa using (shiftBoundAt_freshBelowAt 0 count _
    (substitution_liftN_fresh σ count proposition)).symm

/-- Fusion of substitution lifting with a binder shift.  The substitution on
the left is lifted one additional time because the shifted term has crossed
one additional apparent binder. -/
theorem substitute_liftN_shiftBoundAt (σ : Substitution Γ Ξ)
    (count : Nat) (p : Raw Γ) :
    substitute (Substitution.liftN (count + 1) σ) (shiftBoundAt count p) =
      shiftBoundAt count (substitute (Substitution.liftN count σ) p) := by
  induction p generalizing count with
  | elementary proposition =>
      exact substitution_liftN_succ_as_shift σ count proposition
  | schema slot => rfl
  | bound index => rfl
  | quantified quantifier body ih =>
      simp only [shiftBoundAt, substitute, Substitution.liftN_succ]
      exact congrArg (Raw.quantified quantifier) (ih (count + 1))
  | neg proposition ih =>
      simp only [shiftBoundAt, substitute]
      exact congrArg Raw.neg (ih count)
  | disj left right ihLeft ihRight =>
      simp only [shiftBoundAt, substitute]
      rw [ihLeft count, ihRight count]

theorem substitute_lift_weakenBound (σ : Substitution Γ Ξ) (p : Raw Γ) :
    substitute (Substitution.lift σ) (weakenBound p) =
      weakenBound (substitute σ p) := by
  simpa [weakenBound] using substitute_liftN_shiftBoundAt σ 0 p

/-- Dedicated placeholder substitution for theorem schemas.  Unlike
`Substitution`, this can replace whole canonical Raw matrices. -/
abbrev SchemaSubstitution (Γ : RealContext) := Nat → Raw Γ

def substituteSchema (σ : SchemaSubstitution Γ) : Raw Γ → Raw Γ
  | .elementary proposition => .elementary proposition
  | .schema slot => σ slot
  | .bound index => .bound index
  | .quantified quantifier body =>
      .quantified quantifier
        (substituteSchema (fun slot => weakenBound (σ slot)) body)
  | .neg proposition => .neg (substituteSchema σ proposition)
  | .disj left right => .disj (substituteSchema σ left) (substituteSchema σ right)

def smartNeg : Raw Γ → Raw Γ
  | .quantified .always body => .quantified .sometimes (smartNeg body)
  | .quantified .sometimes body => .quantified .always (smartNeg body)
  | proposition => .neg proposition

def rawSize : Raw Γ → Nat
  | .elementary _ | .schema _ | .bound _ => 1
  | .quantified _ p | .neg p => rawSize p + 1
  | .disj p q => rawSize p + rawSize q + 1

def elementaryExpandedSize : Elementary Γ → Nat
  | .constant _ | .var _ => 1
  | .neg p => elementaryExpandedSize p + 1
  | .disj p q => elementaryExpandedSize p + elementaryExpandedSize q + 1

def expandedSize : Raw Γ → Nat
  | .elementary p => elementaryExpandedSize p
  | .schema _ | .bound _ => 1
  | .quantified _ p | .neg p => expandedSize p + 1
  | .disj p q => expandedSize p + expandedSize q + 1

@[simp] theorem expandedSize_shiftBoundAt (cutoff : Nat) (p : Raw Γ) :
    expandedSize (shiftBoundAt cutoff p) = expandedSize p := by
  induction p generalizing cutoff with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index => by_cases h : cutoff ≤ index <;>
      simp [shiftBoundAt, expandedSize, h]
  | quantified quantifier body ih => simp [shiftBoundAt, expandedSize, ih]
  | neg proposition ih => simp [shiftBoundAt, expandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [shiftBoundAt, expandedSize, ihLeft, ihRight]

@[simp] theorem expandedSize_abstractElementaryAt
    (cutoff : Nat) (p : Elementary (.elementaryProposition :: Γ)) :
    expandedSize (abstractElementaryAt cutoff p) = elementaryExpandedSize p := by
  induction p generalizing cutoff with
  | constant name => rfl
  | var v => cases v <;> rfl
  | neg proposition ih => simp [abstractElementaryAt, expandedSize,
      elementaryExpandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [abstractElementaryAt, expandedSize, elementaryExpandedSize,
        ihLeft, ihRight]

@[simp] theorem expandedSize_abstractOuterAt
    (cutoff : Nat) (p : Raw (.elementaryProposition :: Γ)) :
    expandedSize (abstractOuterAt cutoff p) = expandedSize p := by
  induction p generalizing cutoff with
  | elementary proposition => simp [abstractOuterAt, expandedSize]
  | schema slot => rfl
  | bound index => by_cases h : index ≤ cutoff <;>
      simp [abstractOuterAt, expandedSize, h]
  | quantified quantifier body ih => simp [abstractOuterAt, expandedSize, ih]
  | neg proposition ih => simp [abstractOuterAt, expandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [abstractOuterAt, expandedSize, ihLeft, ihRight]

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

/-- Capture-safe smart disjunction.  `depth` is the number of surrounding
apparent binders already retained by the normalization. -/
def smartDisjScopedAux : Nat → Nat → Raw Γ → Raw Γ → Raw Γ
  | _, 0, p, q => .disj p q
  | depth, fuel + 1, .quantified .always p, .quantified .sometimes q =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux (depth + 2) fuel
          (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)))
  | depth, fuel + 1, .quantified .sometimes p, .quantified .always q =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux (depth + 2) fuel
          (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)))
  | depth, fuel + 1, .quantified quantifier p, q =>
      .quantified quantifier
        (smartDisjScopedAux (depth + 1) fuel p (shiftBoundAt depth q))
  | depth, fuel + 1, p, .quantified quantifier q =>
      .quantified quantifier
        (smartDisjScopedAux (depth + 1) fuel (shiftBoundAt depth p) q)
  | _, _ + 1, p, q => .disj p q

def smartDisjScoped (p q : Raw Γ) : Raw Γ :=
  smartDisjScopedAux 0 (expandedSize p + expandedSize q + 1) p q

def smartImp (p q : Raw Γ) : Raw Γ := smartDisj (smartNeg p) q

theorem abstractOuterAt_smartNeg
    (cutoff : Nat) (p : Raw (.elementaryProposition :: Γ)) :
    abstractOuterAt cutoff (smartNeg p) =
      smartNeg (abstractOuterAt cutoff p) := by
  induction p generalizing cutoff with
  | quantified quantifier body ih =>
      cases quantifier <;>
        simp [smartNeg, abstractOuterAt, ih]
  | elementary proposition =>
      cases proposition with
      | constant name => rfl
      | var v => cases v <;> rfl
      | neg p => rfl
      | disj p q => rfl
  | bound index =>
      by_cases h : index ≤ cutoff <;>
        simp [smartNeg, abstractOuterAt, h]
  | _ => rfl

@[simp] theorem shiftBoundAt_elementary (p : Elementary Γ) :
    shiftBoundAt cutoff (.elementary p) = .elementary p := rfl

@[simp] theorem smartNeg_always (p : Raw Γ) :
    smartNeg (.quantified .always p) = .quantified .sometimes (smartNeg p) := rfl

end PM.CanonicalOrderedFormula
