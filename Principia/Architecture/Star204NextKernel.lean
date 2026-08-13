/-! Restricted strict-order kernel for PM II ✱204, second macro-lot. -/
namespace PM.Architecture.Star204NextKernel
abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def field (R : Rel α) : Set α := fun x => (∃ y,R x y) ∨ ∃ y,R y x
def restrict (R : Rel α) (s : Set α) : Rel α := fun x y => s x ∧ s y ∧ R x y
def initial (R : Rel α) (a : α) : Set α := fun x => R x a
def final (R : Rel α) (a : α) : Set α := fun x => R a x
def Transitive (R : Rel α) := ∀ ⦃x y z⦄, R x y → R y z → R x z
def Irreflexive (R : Rel α) := ∀ x, ¬R x x
def ConnexOn (R : Rel α) (s : Set α) := ∀ ⦃x y⦄, s x → s y → x ≠ y → R x y ∨ R y x
structure SerialOn (R : Rel α) (s : Set α) : Prop where
 trans : Transitive R
 irrefl : Irreflexive R
 connex : ConnexOn R s

theorem star_204_271 (R : Rel α) (s : Set α) (h : SerialOn R s) {x y : α}
    (hx : s x) (hy : s y) : x ≠ y → R x y ∨ R y x := fun hn => h.connex hx hy hn
theorem star_204_272 (R : Rel α) (s : Set α) (h : SerialOn R s) {x y : α} : R x y → ¬R y x := by
 intro hxy hyx; exact h.irrefl x (h.trans hxy hyx)
theorem star_204_3 (R : Rel α) (s : Set α) : ∀ ⦃x⦄, field (restrict R s) x → s x := by
 rintro x (⟨y,h⟩|⟨y,h⟩)
 · exact h.1
 · exact h.2.1
theorem star_204_32 (R : Rel α) (s : Set α) {x y : α} : restrict R s x y → R x y := fun h => h.2.2
theorem star_204_33 (R : Rel α) (s : Set α) {x y : α} : restrict R s x y → s x ∧ s y := fun h => ⟨h.1,h.2.1⟩
theorem star_204_331 (R : Rel α) (s : Set α) {x y : α} (hx : s x) (hy : s y) : R x y → restrict R s x y := fun h => ⟨hx,hy,h⟩
theorem star_204_34 (R : Rel α) (s : Set α) (h : Transitive R) : Transitive (restrict R s) := by
 rintro x y z ⟨hx,_,hxy⟩ ⟨_,hz,hyz⟩; exact ⟨hx,hz,h hxy hyz⟩
theorem star_204_35 (R : Rel α) (s : Set α) (h : Irreflexive R) : Irreflexive (restrict R s) := fun x hx => h x hx.2.2
theorem star_204_4 (R : Rel α) (s : Set α) (h : SerialOn R s) : SerialOn (restrict R s) s := by
 refine ⟨star_204_34 R s h.trans,star_204_35 R s h.irrefl,?_⟩
 intro x y hx hy hn
 rcases h.connex hx hy hn with q | q
 · exact Or.inl ⟨hx,hy,q⟩
 · exact Or.inr ⟨hy,hx,q⟩
theorem star_204_41 (R : Rel α) (s : Set α) {x y : α} : restrict R s x y → s x := fun h => h.1
theorem star_204_42 (R : Rel α) (s : Set α) {x y : α} : restrict R s x y → s y := fun h => h.2.1
theorem star_204_421 (R : Rel α) (s : Set α) {x y : α} : restrict R s x y → R x y := star_204_32 R s
theorem star_204_43 (R : Rel α) (a : α) {x : α} : initial R a x ↔ R x a := Iff.rfl
theorem star_204_44 (R : Rel α) (a : α) {x : α} : final R a x ↔ R a x := Iff.rfl
theorem star_204_45 (R : Rel α) (h : Transitive R) (a : α) {x y : α} : initial R a x → R y x → initial R a y := fun hxa hyx => h hyx hxa
theorem star_204_46 (R : Rel α) (h : Transitive R) (a : α) {x y : α} : final R a x → R x y → final R a y := fun hax hxy => h hax hxy
theorem star_204_461 (R : Rel α) (h : Irreflexive R) (a : α) : ¬initial R a a := h a
theorem star_204_462 (R : Rel α) (h : Irreflexive R) (a : α) : ¬final R a a := h a
end PM.Architecture.Star204NextKernel
