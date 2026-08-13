/-! # PM III, ✱255 — local-source kernel, first distinct tranche -/
namespace PM.FirstEdition.Volume3.Star255LocalKernel

abbrev Rel (α : Sort u) := α → α → Prop
def Converse (R : Rel α) : Rel α := fun x y => R y x
def Union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def EqualRel : Rel α := fun x y => x = y
def Greater (less : Rel α) : Rel α := Converse less
def LessEq (less : Rel α) : Rel α := Union less EqualRel
def OrdinalDomain (Ordinal Cardinal : α → Prop) := fun x => Ordinal x ∧ Cardinal x

theorem star_255_01 (less : Rel α) : less = less := rfl
theorem star_255_02 (less : Rel α) : Greater less = Converse less := rfl
theorem star_255_03 (Ordinal Cardinal : α → Prop) :
    OrdinalDomain Ordinal Cardinal = fun x => Ordinal x ∧ Cardinal x := rfl
theorem star_255_04 (less : Rel α) : LessEq less = Union less EqualRel := rfl

theorem star_255_112 (less : Rel α) {μ ν : α}
    (trichotomy : μ = ν ∨ less μ ν ∨ less ν μ) :
    less μ ν ∨ μ = ν ∨ Greater less μ ν := by
  rcases trichotomy with e|a|b
  · exact Or.inr (Or.inl e)
  · exact Or.inl a
  · exact Or.inr (Or.inr b)

theorem star_255_113 (less : Rel α) {μ ν : α} : Greater less μ ν ↔ less ν μ := Iff.rfl
theorem star_255_114 (less : Rel α) {μ ν : α} : LessEq less μ ν ↔ less μ ν ∨ μ = ν := Iff.rfl
theorem star_255_115 (less : Rel α) {μ ν : α} (h : less μ ν) : LessEq less μ ν := Or.inl h
theorem star_255_12 (less : Rel α) {μ ν : α} (h : μ = ν) : LessEq less μ ν := Or.inr h
theorem star_255_121 (less : Rel α) {μ ν : α} : Greater less μ ν ↔ Converse less μ ν := Iff.rfl
theorem star_255_13 (less : Rel α) {μ ν : α} : LessEq less μ ν ↔ less μ ν ∨ μ = ν := Iff.rfl

theorem star_255_17 (less : Rel α) {P Q : α}
    (h : less Q P) : Greater less P Q := h
theorem star_255_171 (less : Rel α) {μ P : α}
    (h : less μ P) : LessEq less μ P := Or.inl h
theorem star_255_172 (less : Rel α) {μ P : α}
    (h : LessEq less μ P) : less μ P ∨ μ = P := h
theorem star_255_174 (less : Rel α) {μ ν : α}
    (asym : ∀ x y, less x y → ¬ less y x) (h : less μ ν) : ¬ Greater less μ ν := asym μ ν h

end PM.FirstEdition.Volume3.Star255LocalKernel
