/-! # Principia Mathematica I, ✱70 — source model

Relations whose classes of referents and relata belong to prescribed classes.
-/

namespace PM.FirstEdition.Volume1.Star70Source

abbrev Set' (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
abbrev Class (α : Sort u) := Set' α → Prop

def empty : Set' α := fun _ => False
def image (R : Rel α) (y : α) : Set' α := fun x => R x y
def converseImage (R : Rel α) (x : α) : Set' α := fun y => R x y
def nonempty (s : Set' α) : Prop := ∃ x, s x
def Arrow (A B : Class α) (R : Rel α) : Prop :=
  (∀ y, nonempty (image R y) → A (image R y)) ∧
  (∀ x, nonempty (converseImage R x) → B (converseImage R x))
def Converse (R : Rel α) : Rel α := fun x y => R y x
def Inter (A B : Class α) : Class α := fun s => A s ∧ B s
def Union (A B : Class α) : Class α := fun s => A s ∨ B s
def Subclass (A B : Class α) : Prop := ∀ s, A s → B s
def RelUnion (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def disjoint (s t : Set' α) : Prop := ∀ x, ¬ (s x ∧ t x)
def domainRestrict (R : Rel α) (c : Set' α) : Rel α := fun x y => c x ∧ R x y
def rangeRestrict (c : Set' α) (R : Rel α) : Rel α := fun x y => R x y ∧ c y

end PM.FirstEdition.Volume1.Star70Source
