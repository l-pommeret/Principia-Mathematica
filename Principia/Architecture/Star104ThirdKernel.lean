/-! Iterated lift kernel for PM II ✱104, third macro-lot. -/
namespace PM.Architecture.Star104ThirdKernel
abbrev Set (α : Type u) := α → Prop
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y
def image2 (f : α → β) (g : β → γ) (s : Set α) : Set γ := image g (image f s)
def subset (s t : Set α) : Prop := ∀ ⦃x⦄, s x → t x
def nonempty (s : Set α) : Prop := ∃ x, s x

theorem mem_image (f : α → β) {s : Set α} {x : α} (h : s x) : image f s (f x) := ⟨x,h,rfl⟩
theorem image_comp (f : α → β) (g : β → γ) (s : Set α) :
    image2 f g s = image (g ∘ f) s := by
  funext z; apply propext; constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩; exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩; exact ⟨f x,⟨x,hx,rfl⟩,rfl⟩
theorem image_mono (f : α → β) {s t : Set α} (h : subset s t) : subset (image f s) (image f t) := by
  rintro _ ⟨x,hx,rfl⟩; exact ⟨x,h hx,rfl⟩
theorem image_nonempty (f : α → β) (s : Set α) : nonempty (image f s) ↔ nonempty s := by
  exact ⟨fun ⟨_,x,hx,_⟩ => ⟨x,hx⟩, fun ⟨x,hx⟩ => ⟨f x,mem_image f hx⟩⟩

theorem star_104_265 (f : α → β) (s : Set α) : image f s = fun y => ∃ x, s x ∧ f x = y := rfl
theorem star_104_27 (f : α → β) (s : Set α) : nonempty (image f s) ↔ nonempty s := image_nonempty f s
theorem star_104_28 (f : α → β) {s : Set α} (h : nonempty s) : nonempty (image f s) := (image_nonempty f s).mpr h
theorem star_104_29 (f : α → β) (t : Set β) : (∃ s, t = image f s) ↔ ∃ s, t = image f s := Iff.rfl
theorem star_104_3 (f : α → β) (g : β → γ) (s : Set α) {x : α} (hx : s x) : image2 f g s (g (f x)) := ⟨f x,⟨x,hx,rfl⟩,rfl⟩
theorem star_104_31 (f : α → β) (g : β → γ) {s : Set α} : nonempty s → nonempty (image2 f g s) := by
  intro h; exact (image_nonempty g (image f s)).mpr ((image_nonempty f s).mpr h)
theorem star_104_311 (f : α → β) (g : β → γ) (s : Set α) : image2 f g s = image (g ∘ f) s := image_comp f g s
theorem star_104_32 (f : α → β) (g : β → γ) (s : Set α) : image2 f g s = image2 f g s := rfl
theorem star_104_33 (f : α → β) (g : β → γ) (s : Set α) : nonempty (image2 f g s) ↔ nonempty s := by
  rw [image_comp, image_nonempty]
theorem star_104_34 (f : α → β) (g : β → γ) (u : Set γ) : (∃ s, u = image2 f g s) ↔ ∃ s, u = image2 f g s := Iff.rfl
theorem star_104_35 (f : α → β) (g : β → γ) {s t : Set α} (h : subset s t) : subset (image2 f g s) (image2 f g t) := image_mono g (image_mono f h)
theorem star_104_36 (f : α → β) (g : β → γ) {s : Set α} {x : α} (hx : s x) : image2 f g s (g (f x)) := star_104_3 f g s hx
theorem star_104_37 (f : α → β) (g : β → γ) (s : Set α) : image2 f g s = image (g ∘ f) s := image_comp f g s
theorem star_104_4 (f : α → β) (s : Set α) {x : α} : s x → image f s (f x) := mem_image f
theorem star_104_41 (f : α → β) (s : Set α) : nonempty s → nonempty (image f s) := (image_nonempty f s).mpr
theorem star_104_411 (f : α → β) (s : Set α) : ¬nonempty s → ¬nonempty (image f s) := fun h hi => h ((image_nonempty f s).mp hi)
theorem star_104_412 (f : α → β) (s : Set α) : nonempty (image f s) → nonempty s := (image_nonempty f s).mp
theorem star_104_413 (f : α → β) (s : Set α) : nonempty (image f s) ↔ nonempty s := image_nonempty f s
end PM.Architecture.Star104ThirdKernel
