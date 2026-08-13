/-! Type-lift existence kernel for the final propositions of PM II ✱104. -/
namespace PM.Architecture.Star104FinalKernel
abbrev Set (α : Type u) := α → Prop
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y
def nonempty (s : Set α) : Prop := ∃ x, s x
def equivalent (s : Set α) (t : Set β) : Prop :=
  ∃ f : α → β, Function.Injective f ∧ t = image f s

theorem star_104_42 (f : α → β) (hf : Function.Injective f) (s : Set α) :
    equivalent s (image f s) := ⟨f,hf,rfl⟩

theorem star_104_43 (f : α → β) (hf : Function.Injective f) (s : Set α) :
    ∃ t : Set β, equivalent s t := ⟨image f s, star_104_42 f hf s⟩

theorem star_104_44 {s : Set α} {t : Set β} (h : equivalent s t) :
    nonempty t ↔ nonempty s := by
  obtain ⟨f,_,rfl⟩ := h
  constructor
  · rintro ⟨_,x,hx,_⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩; exact ⟨f x,x,hx,rfl⟩

theorem star_104_45 {s : Set α} {t : Set β} (h : equivalent s t) :
    nonempty s → nonempty t := (star_104_44 h).mpr

theorem star_104_46 {s : Set α} {t : Set β} (h : equivalent s t) :
    nonempty t → nonempty s := (star_104_44 h).mp

end PM.Architecture.Star104FinalKernel
