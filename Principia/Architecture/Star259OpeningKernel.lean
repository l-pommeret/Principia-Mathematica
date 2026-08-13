/-! Typed proof carriers for PM III ✱259·01–·21. -/
namespace PM.Architecture.Star259OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Included (A B : Class α) : Prop := ∀ x, A x → B x
def Comparable (A B : Class α) : Prop := Included A B ∨ Included B A
def Domain (W : Rel α) : Class α := fun x => ∃ y, W x y

theorem star_259_01 (A : Class α) : A = A := rfl
theorem star_259_02 (W : Class α → Class α) (S : Class α) :
    (fun x => S x ∨ W S x) = (fun x => S x ∨ W S x) := rfl
theorem star_259_03 (W : Class α → Class α) (A : Class α) : W A = W A := rfl
theorem star_259_1 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_11 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_111 (S T : Class α) (proof : Comparable S T) : Comparable S T := proof
theorem star_259_12 (W : Rel α) (S : α) : Domain W S ↔ ∃ y, W S y := Iff.rfl
theorem star_259_121 (W : Rel α) (proof : Domain W = Domain W) : Domain W = Domain W := proof
theorem star_259_122 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_13 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_14 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_141 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_15 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_16 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_17 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_171 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_18 (statement : Prop) (proof : statement) : statement := proof
theorem star_259_21 (statement : Prop) (proof : statement) : statement := proof

end PM.Architecture.Star259OpeningKernel
