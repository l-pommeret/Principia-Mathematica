import Principia.FirstEdition.Volume3.Star260Source

namespace PM.Architecture.Star260OpeningKernel
abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) := α → α → Prop
def field (P : Relation α) : Class α := fun x => (∃ y, P x y) ∨ ∃ y, P y x
def Least (P : Relation α) (A : Class α) (x : α) := A x ∧ ∀ y, A y → y = x ∨ P x y
def HasLeast (P : Relation α) (A : Class α) := ∃ x, Least P A x
def Bord (P : Relation α) := ∀ A : Class α, (∃ x, A x ∧ field P x) → HasLeast P (fun x => A x ∧ field P x)
def Connex (P : Relation α) := ∀ x y, field P x → field P y → x = y ∨ P x y ∨ P y x
def Transitive (P : Relation α) := ∀ {x y z}, P x y → P y z → P x z
def Series (P : Relation α) := Connex P ∧ Transitive P
def Omega (P : Relation α) := Series P ∧ Bord P
def properSegment (P : Relation α) (a : α) : Class α := fun x => P x a

theorem star_260_01 (P : Relation α) : Bord P ↔ ∀ A : Class α, (∃ x : α, A x ∧ field P x) →
    @HasLeast α P (fun x => A x ∧ field P x) := Iff.rfl
theorem star_260_02 : Omega P ↔ Series P ∧ Bord P := Iff.rfl
theorem star_260_1 (P : Relation α) : Bord P ↔ ∀ A : Class α, (∃ x : α, A x ∧ field P x) →
    ∃ y, @Least α P (fun x => A x ∧ field P x) y := Iff.rfl
theorem star_260_101 (A : Class α) (hP : Bord P) (hA : ∃ x, A x ∧ field P x) :
    ∃ y, Least P (fun x => A x ∧ field P x) y := hP A hA
theorem star_260_102 (h : properSegment P a x) : field P x := Or.inl ⟨a,h⟩

end PM.Architecture.Star260OpeningKernel
