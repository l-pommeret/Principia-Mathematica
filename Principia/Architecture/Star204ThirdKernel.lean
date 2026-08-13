/-! Segment calculus kernel for PM II ✱204, third macro-lot. -/
namespace PM.Architecture.Star204ThirdKernel
abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def initial (R : Rel α) (a : α) : Set α := fun x => R x a
def final (R : Rel α) (a : α) : Set α := fun x => R a x
def closedInitial (R : Rel α) (a : α) : Set α := fun x => R x a ∨ x = a
def closedFinal (R : Rel α) (a : α) : Set α := fun x => R a x ∨ x = a
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def disjoint (s t : Set α) := ∀ x, s x → t x → False
def Transitive (R : Rel α) := ∀ ⦃x y z⦄, R x y → R y z → R x z
def Irreflexive (R : Rel α) := ∀ x, ¬R x x

theorem star_204_463 (R : Rel α) (a : α) : subset (initial R a) (closedInitial R a) := fun {_} h => Or.inl h
theorem star_204_47 (R : Rel α) (a : α) : subset (final R a) (closedFinal R a) := fun {_} h => Or.inl h
theorem star_204_48 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (initial R a) (initial R b) := fun {_} hxa => h hxa hab
theorem star_204_481 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (final R b) (final R a) := fun {_} hbx => h hab hbx
theorem star_204_482 (R : Rel α) (h : Irreflexive R) (a : α) : ¬initial R a a := h a
theorem star_204_483 (R : Rel α) (h : Irreflexive R) (a : α) : ¬final R a a := h a
theorem star_204_5 (R : Rel α) (a : α) {x : α} : closedInitial R a x ↔ R x a ∨ x = a := Iff.rfl
theorem star_204_51 (R : Rel α) (a : α) {x : α} : closedFinal R a x ↔ R a x ∨ x = a := Iff.rfl
theorem star_204_52 (R : Rel α) (a : α) : closedInitial R a a := Or.inr rfl
theorem star_204_53 (R : Rel α) (a : α) : closedFinal R a a := Or.inr rfl
theorem star_204_54 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (closedInitial R a) (initial R b) := by
 rintro x (hxa|rfl); exact h hxa hab; exact hab
theorem star_204_55 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (closedFinal R b) (final R a) := by
 rintro x (hbx|rfl); exact h hab hbx; exact hab
theorem star_204_551 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (closedInitial R a) (closedInitial R b) := fun {_} hx => Or.inl (star_204_54 R h hab hx)
theorem star_204_56 (R : Rel α) (h : Transitive R) {a b : α} (hab : R a b) : subset (closedFinal R b) (closedFinal R a) := fun {_} hx => Or.inl (star_204_55 R h hab hx)
theorem star_204_561 (R : Rel α) (ht : Transitive R) (h : Irreflexive R) (a : α) : disjoint (initial R a) (closedFinal R a) := by
 intro x hxa hax; rcases hax with hax|rfl
 · exact h x (ht hxa hax)
 · exact h x hxa
theorem star_204_562 (R : Rel α) (ht : Transitive R) (h : Irreflexive R) (a : α) : disjoint (final R a) (closedInitial R a) := by
 intro x hax hxa; rcases hxa with hxa|rfl
 · exact h a (ht hax hxa)
 · exact h x hax
theorem star_204_57 (R : Rel α) (a : α) : subset (initial R a) (closedInitial R a) := star_204_463 R a
theorem star_204_58 (R : Rel α) (a : α) : subset (final R a) (closedFinal R a) := star_204_47 R a
end PM.Architecture.Star204ThirdKernel
