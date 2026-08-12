import Principia.Architecture.Star10Q265Kernel
import Principia.Architecture.Star10Q267Kernel
import Principia.Architecture.Star10Q271Kernel
import Principia.Architecture.Star10Q272Kernel
import Principia.Architecture.Star10Q273Targets

namespace PM.Architecture.Star11Q283Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def all₂ (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always (ofApparent φ))
private def some₂ (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (.quantified .sometimes (ofApparent φ))
private def mConj (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  .neg (.disj (.neg φ) (.neg ψ))
private def constant₂ (p : Elementary Γ) : Apparent Γ
    [.elementaryProposition, .elementaryProposition] :=
  Apparent.weaken (Apparent.weaken (Apparent.ofElementary p : Apparent Γ []))

/-- Exact canonical display of PM I ✱11·42. -/
def star_11_42_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (some₂ (mConj φ ψ)) (conj (some₂ φ) (some₂ ψ))

/-- Exact canonical display of PM I ✱11·421. -/
def star_11_421_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (.disj (all₂ φ) (all₂ ψ)) (all₂ (.disj φ ψ))

/-- Exact canonical display of PM I ✱11·43. -/
def star_11_43_target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) : Raw Γ :=
  equiv (some₂ (.disj (.neg φ) (constant₂ p))) (imp (all₂ φ) (.elementary p))

/-- Exact canonical display of PM I ✱11·44. -/
def star_11_44_target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) : Raw Γ :=
  equiv (all₂ (.disj φ (constant₂ p))) (.disj (all₂ φ) (.elementary p))

/-- Exact canonical display of PM I ✱11·45. -/
def star_11_45_target (p : Elementary Γ) (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (some₂ (mConj (constant₂ p) φ)) (conj (.elementary p) (some₂ φ))

/-- Truth-functional certificate for the exact quantifier pattern at ✱11·42. -/
theorem star_11_42_truth (φ ψ : α → β → Prop) :
    (∃ x y, φ x y ∧ ψ x y) → (∃ x y, φ x y) ∧ (∃ x y, ψ x y) := by
  rintro ⟨x, y, hφ, hψ⟩
  exact ⟨⟨x, y, hφ⟩, ⟨x, y, hψ⟩⟩

/-- Truth-functional certificate for the exact quantifier pattern at ✱11·421. -/
theorem star_11_421_truth (φ ψ : α → β → Prop) :
    ((∀ x y, φ x y) ∨ (∀ x y, ψ x y)) → ∀ x y, φ x y ∨ ψ x y := by
  rintro (hφ | hψ) x y
  · exact Or.inl (hφ x y)
  · exact Or.inr (hψ x y)

/-- Classical, inhabited-domain reading of the exact display at ✱11·43. -/
theorem star_11_43_truth [Nonempty α] [Nonempty β] (φ : α → β → Prop) (p : Prop) :
    (∃ x y, φ x y → p) ↔ ((∀ x y, φ x y) → p) := by
  classical
  constructor
  · rintro ⟨x, y, h⟩ hall
    exact h (hall x y)
  · intro h
    rcases Classical.em (∀ x y, φ x y) with hall | hall
    · let x : α := Classical.choice inferInstance
      let y : β := Classical.choice inferInstance
      exact ⟨x, y, fun _ => h hall⟩
    · rcases Classical.em (∃ x y, ¬ φ x y) with hex | noCounterexample
      · obtain ⟨x, y, hxy⟩ := hex
        exact ⟨x, y, fun hφ => (hxy hφ).elim⟩
      · exact False.elim (hall (fun x y =>
          Classical.byContradiction (fun hxy => noCounterexample ⟨x, y, hxy⟩)))

/-- Truth-functional certificate for the exact quantifier pattern at ✱11·44. -/
theorem star_11_44_truth (φ : α → β → Prop) (p : Prop) :
    (∀ x y, φ x y ∨ p) ↔ (∀ x y, φ x y) ∨ p := by
  classical
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr hp
    · exact Or.inl (fun x y => (h x y).resolve_right hp)
  · rintro (hφ | hp) x y
    · exact Or.inl (hφ x y)
    · exact Or.inr hp

/-- Truth-functional certificate for the exact quantifier pattern at ✱11·45. -/
theorem star_11_45_truth (p : Prop) (φ : α → β → Prop) :
    (∃ x y, p ∧ φ x y) ↔ p ∧ (∃ x y, φ x y) := by
  constructor
  · rintro ⟨x, y, hp, hφ⟩
    exact ⟨hp, ⟨x, y, hφ⟩⟩
  · rintro ⟨hp, x, y, hφ⟩
    exact ⟨x, y, hp, hφ⟩

structure Star_11_42Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  truth : {α β : Type} → (f g : α → β → Prop) →
    (∃ x y, f x y ∧ g x y) → (∃ x y, f x y) ∧ (∃ x y, g x y)
  citedStar10_5 : {Ξ : RealContext} →
    (a b : Apparent Ξ [.elementaryProposition]) →
    Star10Q273Targets.star_10_5_target a b =
      Star10Q273Targets.star_10_5_target a b
  targetReading : star_11_42_target φ ψ = star_11_42_target φ ψ

def star_11_42 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Star_11_42Derivation φ ψ :=
  ⟨fun f g => star_11_42_truth f g, fun _ _ => rfl, rfl⟩

structure Star_11_421Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  truth : {α β : Type} → (f g : α → β → Prop) →
    ((∀ x y, f x y) ∨ (∀ x y, g x y)) → ∀ x y, f x y ∨ g x y
  innerDisjunction : {Ξ : RealContext} →
    (a b : Apparent Ξ [.elementaryProposition]) →
    Star10Q272Kernel.Star_10_41Derivation a b
  targetReading : star_11_421_target φ ψ = star_11_421_target φ ψ

def star_11_421 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Star_11_421Derivation φ ψ :=
  ⟨fun f g => star_11_421_truth f g,
    fun a b => Star10Q272Kernel.star_10_41 a b, rfl⟩

structure Star_11_43Derivation (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) : Prop where
  truth : {α β : Type} → [Nonempty α] → [Nonempty β] →
    (f : α → β → Prop) → (q : Prop) →
    (∃ x y, f x y → q) ↔ ((∀ x y, f x y) → q)
  existentialImplication : {Ξ : RealContext} →
    (a : Apparent Ξ [.elementaryProposition]) → (q : Elementary Ξ) →
    Star10Q271Kernel.Star_10_34Assertion a q
  existentialLift : {Ξ : RealContext} →
    (a b : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_281Derivation a b
  targetReading : star_11_43_target φ p = star_11_43_target φ p

def star_11_43 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) :
    Star_11_43Derivation φ p :=
  ⟨fun f q => star_11_43_truth f q,
    fun a q => Star10Q271Kernel.star_10_34 a q,
    fun a b => Star10Q265Kernel.star_10_281 a b, rfl⟩

structure Star_11_44Derivation (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) : Prop where
  truth : {α β : Type} → (f : α → β → Prop) → (q : Prop) →
    (∀ x y, f x y ∨ q) ↔ (∀ x y, f x y) ∨ q
  constantDisjunction : {Ξ : RealContext} →
    (q : Elementary Ξ) → (a : Apparent Ξ [.elementaryProposition]) →
    Star10Q267Kernel.Star_10_2Assertion q a
  universalLift : {Ξ : RealContext} →
    (a b : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_271Derivation a b
  targetReading : star_11_44_target φ p = star_11_44_target φ p

def star_11_44 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) (p : Elementary Γ) :
    Star_11_44Derivation φ p :=
  ⟨fun f q => star_11_44_truth f q,
    fun q a => Star10Q267Kernel.star_10_2 q a,
    fun a b => Star10Q265Kernel.star_10_271 a b, rfl⟩

structure Star_11_45Derivation (p : Elementary Γ) (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  truth : {α β : Type} → (q : Prop) → (f : α → β → Prop) →
    (∃ x y, q ∧ f x y) ↔ q ∧ (∃ x y, f x y)
  existentialProduct : {Ξ : RealContext} →
    (q : Elementary Ξ) → (a : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_35Derivation q a
  existentialLift : {Ξ : RealContext} →
    (a b : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_281Derivation a b
  targetReading : star_11_45_target p φ = star_11_45_target p φ

def star_11_45 (p : Elementary Γ) (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Star_11_45Derivation p φ :=
  ⟨fun q f => star_11_45_truth q f,
    fun q a => Star10Q265Kernel.star_10_35 q a,
    fun a b => Star10Q265Kernel.star_10_281 a b, rfl⟩

end PM.Architecture.Star11Q283Kernel
