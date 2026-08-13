/-! Cardinal-preservation kernel for the end of PM II ✱213. -/
namespace PM.Architecture.Star213FinalKernel
abbrev Set (α : Type u) := α → Prop
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y
def nonempty (s : Set α) := ∃ x, s x

theorem star_213_57 (f : α → β) (s : Set α) :
    nonempty (image f s) ↔ nonempty s := by
 constructor
 · rintro ⟨_,x,hx,_⟩; exact ⟨x,hx⟩
 · rintro ⟨x,hx⟩; exact ⟨f x,x,hx,rfl⟩

theorem star_213_58 (f : α → β) (s : Set α) :
    nonempty s → nonempty (image f s) := (star_213_57 f s).mpr

end PM.Architecture.Star213FinalKernel
