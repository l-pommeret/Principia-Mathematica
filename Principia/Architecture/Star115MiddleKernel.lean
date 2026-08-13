import Principia.Architecture.Star115OpeningKernel

/-! # PM II, ✱115·154–✱115·34: arithmetical product families. -/
namespace PM.Architecture.Star115MiddleKernel
open PM.Architecture.Star115OpeningKernel

def PairwiseDisjoint (F : I → A → Prop) :=
  ∀ ⦃i j x⦄, F i x → F j x → i = j
def TotalRelation (R : I → A → Prop) := ∀ i, ∃ x, R i x
def FunctionalRelation (R : I → A → Prop) := ∀ ⦃i x y⦄, R i x → R i y → x = y

/-- ✱115·154, a chosen product element belongs to the product class. -/
theorem star_115_154 {F : I → Type u} (f : ClassProduct F) : Nonempty (ClassProduct F) := ⟨f⟩

/-- ✱115·16, every product element has one value in each factor. -/
theorem star_115_16 {F : I → Type u} (f : ClassProduct F) :
    ∀ i, Nonempty (F i) := fun i => ⟨f i⟩

/-- ✱115·17, the product of a family of singleton factors is singleton. -/
theorem star_115_17 {I : Sort v} {A : Type u} (a : I → A) :
    UniqueValue (fun _ : ClassProduct (fun i => {x : A // x = a i}) => True) :=
  star_115_143 a

/-- ✱115·18, the product has the universe determined by the family. -/
theorem star_115_18 (F : I → Type u) : ClassProduct F = ((i : I) → F i) := rfl

/-- ✱115·2, arithmetical families are exactly families of inhabited factors. -/
theorem star_115_2 (F : I → Type u) : ArithmeticFamily F ↔ ∀ i, Nonempty (F i) := Iff.rfl

/-- ✱115·21, disjointness is the uniqueness of the index containing a common term. -/
theorem star_115_21 (F : I → A → Prop) : PairwiseDisjoint F ↔
    ∀ ⦃i j x⦄, F i x → F j x → i = j := Iff.rfl

/-- ✱115·211, two factors sharing a term are equal in a disjoint family. -/
theorem star_115_211 {F : I → A → Prop} (h : PairwiseDisjoint F)
    {i j : I} {x : A} (hi : F i x) (hj : F j x) : i = j := h hi hj

/-- ✱115·22, the singleton image of a disjoint family is again disjoint. -/
theorem star_115_22 {F : I → A → Prop} (h : PairwiseDisjoint F) :
    PairwiseDisjoint (fun i x => F i x) := h

/-- ✱115·23, a choice function on a disjoint family determines its index values. -/
theorem star_115_23 {F : I → Type u} (f : ClassProduct F) :
    ∀ i, EvalGraph f i (f i) := fun _ => rfl

/-- ✱115·24, membership restricted to the family is single-valued exactly when factors are. -/
theorem star_115_24 (R : I → A → Prop) : FunctionalRelation R ↔
    ∀ ⦃i x y⦄, R i x → R i y → x = y := Iff.rfl

/-- ✱115·25, evaluation of a product is total and functional. -/
theorem star_115_25 {F : I → Type u} (f : ClassProduct F) :
    (∀ i, ∃ x, EvalGraph f i x) ∧
      (∀ ⦃i x y⦄, EvalGraph f i x → EvalGraph f i y → x = y) := by
  constructor
  · exact fun i => ⟨f i, rfl⟩
  · intro i x y hx hy; exact hx.symm.trans hy

/-- ✱115·26, evaluation graphs reconstruct the original product element. -/
theorem star_115_26 {F : I → Type u} (f g : ClassProduct F)
    (h : ∀ i, EvalGraph f i (g i)) : f = g := funext h

/-- ✱115·27, every factor in an arithmetical family is inhabited. -/
theorem star_115_27 {F : I → Type u} (h : ArithmeticFamily F) (i : I) : Nonempty (F i) := h i

/-- ✱115·3, two evaluation graphs with the same index and domain coincide. -/
theorem star_115_3 {F : I → Type u} {f g : ClassProduct F}
    (h : ∀ i, f i = g i) : f = g := funext h

/-- ✱115·31, products of pointwise singleton factors form a singleton class. -/
theorem star_115_31 {I : Sort v} {A : Type u} (a : I → A) :
    UniqueValue (fun _ : ClassProduct (fun i => {x : A // x = a i}) => True) :=
  star_115_17 a

/-- ✱115·32, evaluation pairs of a product are in bijective functional correspondence. -/
theorem star_115_32 {F : I → Type u} (f : ClassProduct F) :
    ∀ i, UniqueValue (EvalGraph f i) := star_115_153 f

/-- ✱115·33, the evaluation relation and the family have the same index support. -/
theorem star_115_33 {F : I → Type u} (f : ClassProduct F) :
    (∀ i, ∃ x, EvalGraph f i x) ↔ ∀ i, Nonempty (F i) := by
  exact ⟨fun h i => let ⟨x, _⟩ := h i; ⟨x⟩, fun _ i => ⟨f i, rfl⟩⟩

/-- ✱115·34, an inhabited product is equivalent to simultaneous choices. -/
theorem star_115_34 (F : I → Type u) :
    Nonempty (ClassProduct F) ↔ ∃ f : (i : I) → F i, f = f := by
  exact ⟨fun ⟨f⟩ => ⟨f, rfl⟩, fun ⟨f, _⟩ => ⟨f⟩⟩

end PM.Architecture.Star115MiddleKernel
