import Principia.Architecture.Star206OpeningKernel
namespace PM.Architecture.Star206LaterKernel
open PM.Architecture.Star206OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Image (P : Rel α) (a : Class α) : Class α := fun y=>∃x,a x∧P x y
def Transitive (P : Rel α) := ∀x y z,P x y→P y z→P x z
def Irreflexive (P : Rel α) := ∀x,¬P x x
theorem star_206_25 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := fun _ h=>h.2
theorem star_206_26 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → Field P x := fun h=>h.2
theorem star_206_27 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → LowerBound P (Inter a (Field P)) x := fun h=>h.1
theorem star_206_28 (P : Rel α) (a : Class α) : Sequent P a = Sequent P (Inter a (Field P)) := star_206_131 P a
theorem star_206_3 (P : Rel α) (a : Class α) (x : α) : Sequent P a x ↔ Sequent P a x := Iff.rfl
theorem star_206_31 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Field P x := h.2
theorem star_206_32 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : ∀y,a y∧Field P y→P y x := h.1
theorem star_206_33 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := fun _ h=>h.2
theorem star_206_331 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → ¬Empty (Field P) := by intro h e; exact e x h.2
theorem star_206_34 (P : Rel α) (a : Class α) (h : Empty (Inter a (Field P))) : Sequent P a = Field P := star_206_14 P a h
theorem star_206_35 (P : Rel α) (a : Class α) (ha : Included a (Field P)) : Sequent P a = fun x=>LowerBound P a x∧Field P x := star_206_143 P a ha
theorem star_206_36 (P : Rel α) (a : Class α) (x : α) (hi : Irreflexive P) (h : Sequent P a x) : ¬P x x := hi x
theorem star_206_37 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Included (Inter a (Field P)) (fun y=>P y x) := h.1
theorem star_206_38 (P : Rel α) (a : Class α) : Sequent P a = fun x=>Sequent P a x := rfl
theorem star_206_4 (P : Rel α) (x : α) (hx : Field P x) (h : P x x) : P x x := h
theorem star_206_401 (P : Rel α) (x : α) (h : P x x) : ∃y,P x y := ⟨x,h⟩
theorem star_206_41 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Field P x := h.2
theorem star_206_42 (P : Rel α) (x : α) : Sequent P (fun y=>y=x) = Sequent P (Inter (fun y=>y=x) (Field P)) := star_206_131 P _
end PM.Architecture.Star206LaterKernel
