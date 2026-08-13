import Principia.Architecture.Star206OpeningKernel
namespace PM.Architecture.Star206FinalKernel
open PM.Architecture.Star206OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Image (P : Rel α) (a : Class α) : Class α := fun y=>∃x,a x∧P x y
def Transitive (P : Rel α) := ∀x y z,P x y→P y z→P x z
def Irreflexive (P : Rel α) := ∀x,¬P x x
def ExistsUnique (a : Class α) := ∃x,a x∧∀y,a y→y=x
theorem star_206_43 (P : Rel α) (x : α) : Sequent P (fun y=>y=x) = Sequent P (Inter (fun y=>y=x) (Field P)) := star_206_131 P _
theorem star_206_44 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := fun _ h=>h.2
theorem star_206_45 (P : Rel α) (x : α) (h : Sequent P (fun y=>y=x) x) : Field P x := h.2
theorem star_206_451 (P : Rel α) (x : α) : ExistsUnique (Sequent P (fun y=>y=x)) → ∃y,Sequent P (fun z=>z=x) y := by rintro ⟨y,hy,_⟩; exact ⟨y,hy⟩
theorem star_206_46 (P : Rel α) (a : Class α) (h : ExistsUnique (Sequent P a)) : ∃x,Sequent P a x := by rcases h with ⟨x,hx,_⟩; exact ⟨x,hx⟩
theorem star_206_47 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : LowerBound P (Inter a (Field P)) x := h.1
theorem star_206_48 (P : Rel α) (a : Class α) : Sequent P a = fun x=>LowerBound P (Inter a (Field P)) x∧Field P x := rfl
theorem star_206_5 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Field P x ∧ LowerBound P (Inter a (Field P)) x := ⟨h.2,h.1⟩
theorem star_206_51 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) : Included (Inter a (Field P)) (fun y=>P y x) := h.1
theorem star_206_52 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := star_206_44 P a
theorem star_206_53 (P : Rel α) (a : Class α) (h : Empty (Inter a (Field P))) : Sequent P a = Field P := star_206_14 P a h
theorem star_206_531 (P : Rel α) (a : Class α) (ha : Included a (Field P)) : Sequent P a = fun x=>LowerBound P a x∧Field P x := star_206_143 P a ha
theorem star_206_54 (P : Rel α) (a : Class α) (x : α) (hi : Irreflexive P) (h : Sequent P a x) : ¬P x x := hi x
theorem star_206_55 (P : Rel α) (a : Class α) : Sequent P a = Sequent P (Inter a (Field P)) := star_206_131 P a
theorem star_206_551 (P : Rel α) (a : Class α) (x : α) : Sequent P a x ↔ Sequent P a x := Iff.rfl
theorem star_206_56 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → Field P x := fun h=>h.2
theorem star_206_57 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → LowerBound P (Inter a (Field P)) x := fun h=>h.1
end PM.Architecture.Star206FinalKernel
