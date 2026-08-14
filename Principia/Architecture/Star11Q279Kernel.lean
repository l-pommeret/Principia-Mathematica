import Principia.Architecture.Star11Q275Definitions
import Principia.Architecture.CanonicalNormalization
import Principia.Architecture.Star10Q269Kernel

namespace PM.Architecture.Star11Q279Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization

/-! The following notation is object-language syntax: every displayed
operator constructs canonical `Raw`, rather than abbreviating a Lean `Prop`. -/

local prefix:max "∼ᵣ" => Raw.neg
private def conjunctionRaw (left right : Raw Γ) : Raw Γ :=
  .neg (.disj (.neg left) (.neg right))
private def equivalenceRaw (left right : Raw Γ) : Raw Γ :=
  conjunctionRaw (rawImp left right) (rawImp right left)
local infix:50 " ≡ᵣ " => equivalenceRaw
local notation:max "(∃₂ " φ ")" =>
  Raw.quantified Quantifier.sometimes
    (Raw.quantified Quantifier.sometimes (ofApparent φ))
local notation:max "(∀₂ " φ ")" =>
  Raw.quantified Quantifier.always
    (Raw.quantified Quantifier.always (ofApparent φ))

/-- PM I ✱11·25 in canonical PM object syntax.  The left and right members
render respectively as `∼{(∃x,y).φ(x,y)}` and `(x,y).∼φ(x,y)`. -/
def star_11_25_raw
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) :
    Raw Γ × Raw Γ :=
  (∼ᵣ (∃₂ φ), (∀₂ (∼ₐ φ)))

/-- The exact asserted formula printed at ✱11·25, not merely its two members. -/
def star_11_25_target
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  (star_11_25_raw φ).1 ≡ᵣ (star_11_25_raw φ).2

/-- The two successive source-authorized quantifier-negation steps behind
✱11·25.  This is checked syntax normalization, not a free-text rendering. -/
theorem star_11_25_normalization
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) :
    NormalizesScoped (∼ᵣ (∃₂ φ)) (∀₂ (∼ₐ φ)) := by
  exact .trans
    (.negSometimes (.quantified .sometimes (ofApparent φ)))
    (.alwaysCongr (.negSometimes (ofApparent φ)))

/-- Source-critical certificate for PM I ✱11·25.  Its normalization is the two
successive transposed quantifier-negation steps, and `unaryCase` exposes the
already audited ✱10·252 certificate used at each unary stage. -/
structure Star_11_25Derivation
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Prop where
  normalization : NormalizesScoped
    (star_11_25_raw φ).1 (star_11_25_raw φ).2
  unaryCase : {Ξ : RealContext} →
    (ψ : Apparent Ξ [.elementaryProposition]) →
      Star10Q269Kernel.Star_10_252Assertion ψ
  targetReading : star_11_25_target φ = star_11_25_target φ

/-- PM I ✱11·25, canonical syntax-level derivational certificate. -/
def star_11_25
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) :
    Star_11_25Derivation φ where
  normalization := star_11_25_normalization φ
  unaryCase := fun ψ => Star10Q269Kernel.star_10_252 ψ
  targetReading := rfl

/-- Secondary ordinary-`Prop` interpretation of ✱11·25. -/
theorem star_11_25_prop (φ : α → β → Prop) :
    (¬ ∃ x y, φ x y) ↔ ∀ x y, ¬ φ x y := by
  constructor
  · intro h x y hxy
    exact h ⟨x, y, hxy⟩
  · intro h hex
    obtain ⟨x, y, hxy⟩ := hex
    exact h x y hxy

/-- Secondary ordinary-`Prop` reading of PM I ✱11·26.  A canonical PM
derivation still requires composition of the printed ✱10·1·28 and
✱10·11·21 steps at the binary apparent-function carrier. -/
theorem star_11_26_prop (φ : α → β → Prop) :
    (∃ x, ∀ y, φ x y) → ∀ y, ∃ x, φ x y := by
  rintro ⟨x, hx⟩ y
  exact ⟨x, hx y⟩

/-- Secondary ordinary-`Prop` reading of the first adjacent equivalence in
PM I ✱11·27. -/
theorem star_11_27_left_prop (φ : α → β → γ → Prop) :
    (∃ x y, ∃ z, φ x y z) ↔ ∃ x, ∃ y z, φ x y z := by
  rfl

/-- Secondary ordinary-`Prop` reading of the second adjacent equivalence in
PM I ✱11·27. -/
theorem star_11_27_prop (φ : α → β → γ → Prop) :
    (∃ x, ∃ y z, φ x y z) ↔ ∃ x y z, φ x y z := by
  rfl

/-- Secondary ordinary-`Prop` reading of PM I ✱11·3. -/
theorem star_11_3_prop (p : Prop) (φ : α → β → Prop) :
    (p → ∀ x y, φ x y) ↔ ∀ x y, p → φ x y := by
  constructor
  · intro h x y hp
    exact h hp x y
  · intro h hp x y
    exact h x y hp

/-- Secondary ordinary-`Prop` reading of PM I ✱11·31. -/
theorem star_11_31_prop (φ ψ : α → β → Prop) :
    ((∀ x y, φ x y) ∧ (∀ x y, ψ x y)) ↔ ∀ x y, φ x y ∧ ψ x y := by
  constructor
  · rintro ⟨hφ, hψ⟩ x y
    exact ⟨hφ x y, hψ x y⟩
  · intro h
    exact ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩

end PM.Architecture.Star11Q279Kernel
