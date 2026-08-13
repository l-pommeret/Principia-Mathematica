import Principia.Architecture.Star206OpeningKernel
namespace PM.Architecture.Star206MiddleKernel
open PM.Architecture.Star206OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def ExistsUnique (a : Class α) := ∃ x,a x ∧ ∀ y,a y → y=x
def Image (P : Rel α) (a : Class α) : Class α := fun y=>∃x,a x∧P x y
def Transitive (P : Rel α) := ∀x y z,P x y→P y z→P x z
theorem star_206_161 (P : Rel α) (a : Class α) (h : AtMostOne (Sequent P a)) : AtMostOne (Sequent P a) := h
theorem star_206_17 (P : Rel α) (a : Class α) (x : α) : Sequent P a x ↔ LowerBound P (Inter a (Field P)) x ∧ Field P x := Iff.rfl
theorem star_206_171 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Field P x := h.2
theorem star_206_172 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : LowerBound P (Inter a (Field P)) x := h.1
theorem star_206_173 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := fun _ h=>h.2
theorem star_206_174 (P : Rel α) (a : Class α) (h : AtMostOne (Sequent P a)) : AtMostOne (Sequent P a) := h
theorem star_206_18 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := star_206_173 P a
theorem star_206_181 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → Field P x := fun h=>h.2
theorem star_206_2 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → LowerBound P (Inter a (Field P)) x := fun h=>h.1
theorem star_206_21 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : ∀y,a y∧Field P y→P y x := h.1
theorem star_206_211 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Included (Inter a (Field P)) (fun y=>P y x) := h.1
theorem star_206_212 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Field P x := h.2
theorem star_206_213 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Included (Inter a (Field P)) (fun y=>P y x) := h.1
theorem star_206_22 (P : Rel α) (a : Class α) (x : α) (ht : Transitive P) (h : Sequent P a x) : LowerBound P (Inter a (Field P)) x := h.1
theorem star_206_23 (P : Rel α) (a : Class α) (x : α) (ht : Transitive P) (h : Sequent P a x) : Field P x := h.2
theorem star_206_24 (P : Rel α) (a : Class α) : Sequent P a = Sequent P (Inter a (Field P)) := star_206_131 P a
end PM.Architecture.Star206MiddleKernel
