import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Star11Q277Targets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))

/-- The two successive binders of ✱11·01, embedded in the canonical carrier. -/
def all₂ (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always (ofApparent φ))

/-- Exchange exactly the two apparent variables of a binary matrix. -/
def swap₂ : Apparent.Renaming
    [.elementaryProposition, .elementaryProposition]
    [.elementaryProposition, .elementaryProposition]
  | .zero => .succ .zero
  | .succ .zero => .zero

/-- The value `φ(z,w)`, obtained by two capture-safe instantiations. -/
def value₂ (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition])
    (z w : RealVar Γ .elementaryProposition) : Elementary Γ :=
  Apparent.closedToElementary
    (Apparent.instantiate (Apparent.instantiate φ (.real z)) (.real w))

/-- PM I ✱11·07, the exact binary-permutation primitive endpoint. -/
def star_11_07_target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all₂ φ) (all₂ (Apparent.rename swap₂ φ))

/-- PM I ✱11·1, binary universal instantiation at the displayed `z,w`. -/
def star_11_1_target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition])
    (z w : RealVar Γ .elementaryProposition) : Raw Γ :=
  imp (all₂ φ) (.elementary (value₂ φ z w))

/-- PM I ✱11·11 is metalinguistic.  This record is its exact premise and
conclusion contract; it deliberately supplies no unlicensed higher-order
generalization operation. -/
structure Star_11_11Target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) where
  premise : Raw Γ
  conclusion : Raw Γ
  premise_is_open_values : premise = all₂ φ
  conclusion_is_binary_generalization : conclusion = all₂ φ

def star_11_11_target (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Star_11_11Target φ :=
  ⟨all₂ φ, all₂ φ, rfl, rfl⟩

/-- PM I ✱11·12.  The elementary `p` is explicitly weakened through both
matrix slots before the two universal binders are closed. -/
def star_11_12_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all₂ (.disj (Apparent.ofElementary p) φ))
    (.disj (.elementary p) (all₂ φ))

/-- Exact premise/conclusion syntax of the metalinguistic rule ✱11·13. -/
structure Star_11_13Target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) where
  leftPremise : Raw Γ
  rightPremise : Raw Γ
  conclusion : Raw Γ
  left_is_universal : leftPremise = all₂ φ
  right_is_universal : rightPremise = all₂ ψ
  conclusion_is_pointwise_product : conclusion = all₂ (.neg (.disj (.neg φ) (.neg ψ)))

def star_11_13_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Star_11_13Target φ ψ :=
  ⟨all₂ φ, all₂ ψ, all₂ (.neg (.disj (.neg φ) (.neg ψ))), rfl, rfl, rfl⟩

/-- PM I ✱11·14, simultaneous specialization of two binary universals. -/
def star_11_14_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition])
    (z w : RealVar Γ .elementaryProposition) : Raw Γ :=
  imp (conj (all₂ φ) (all₂ ψ))
    (conj (.elementary (value₂ φ z w)) (.elementary (value₂ ψ z w)))

end PM.Architecture.Star11Q277Targets
