/-! Injective type-lift kernel for PM II ✱104, second macro-lot. -/
namespace PM.Architecture.Star104NextKernel
abbrev Set (α : Type u) := α → Prop
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y
def nonempty (s : Set α) : Prop := ∃ x, s x
def subset (s t : Set α) : Prop := ∀ ⦃x⦄, s x → t x
def disjoint (s t : Set α) : Prop := ∀ x, s x → t x → False

theorem image_mem (f : α → β) (s : Set α) {x : α} (hx : s x) : image f s (f x) := ⟨x,hx,rfl⟩
theorem image_mono (f : α → β) {s t : Set α} (h : subset s t) : subset (image f s) (image f t) := by
  rintro y ⟨x,hx,rfl⟩; exact ⟨x,h hx,rfl⟩
theorem image_injective (f : α → β) (hf : Function.Injective f) {s t : Set α} :
    image f s = image f t ↔ s = t := by
  constructor
  · intro h; funext x; apply propext; constructor
    · intro hx; have : image f t (f x) := congrFun h (f x) ▸ image_mem f s hx
      obtain ⟨y,hy,he⟩ := this; exact hf he ▸ hy
    · intro hx; have : image f s (f x) := congrFun h (f x) ▸ image_mem f t hx
      obtain ⟨y,hy,he⟩ := this; exact hf he ▸ hy
  · rintro rfl; rfl

theorem star_104_141 (f : α → β) (hf : Function.Injective f) : Function.Injective (image f) :=
  fun _ _ h => (image_injective f hf).mp h
theorem star_104_142 (f : α → β) (hf : Function.Injective f) {s t : Set α} :
    image f s = image f t → s = t := (image_injective f hf).mp
theorem star_104_15 (f : α → β) (s : Set α) : ∃ t, t = image f s := ⟨_,rfl⟩
theorem star_104_2 (f : α → β) (s : Set α) : subset s (fun x => image f s (f x)) :=
  fun {_} hx => image_mem f s hx
theorem star_104_201 (f : α → β) {s t : Set α} (h : subset s t) : subset (image f s) (image f t) := image_mono f h
theorem star_104_211 (f : α → β) {s : Set α} : nonempty s → nonempty (image f s) := by
  rintro ⟨x,hx⟩; exact ⟨f x,image_mem f s hx⟩
theorem star_104_23 (f : α → β) (s : Set α) {x : α} (hx : s x) : image f s (f x) := image_mem f s hx
theorem star_104_231 (f : α → β) (hf : Function.Injective f) {s t : Set α} : image f s = image f t → s = t := (image_injective f hf).mp
theorem star_104_232 (f : α → β) (hf : Function.Injective f) {s t : Set α} : image f s = image f t ↔ s = t := image_injective f hf
theorem star_104_24 (f : α → β) (s : Set α) : image f s = image f s := rfl
theorem star_104_25 (f : α → β) : ∀ s : Set α, ∃ t, t = image f s := fun s => ⟨_,rfl⟩
theorem star_104_251 (f : α → β) (s : Set α) : ¬ nonempty s → ¬ nonempty (image f s) := by
  intro h ⟨_,x,hx,_⟩; exact h ⟨x,hx⟩
theorem star_104_252 (f : α → β) (hf : Function.Injective f) {s t : Set α}
    (h : disjoint s t) : disjoint (image f s) (image f t) := by
  intro y ⟨x,hx,he⟩ ⟨z,hz,he'⟩
  have hxz : x = z := hf (he.trans he'.symm)
  subst z
  exact h x hx hz
theorem star_104_26 (f : α → β) (s : Set α) : image f s = image f s := rfl
theorem star_104_261 (f : α → β) {s t : Set α} (h : subset s t) : subset (image f s) (image f t) := image_mono f h
theorem star_104_262 (f : α → β) (hf : Function.Injective f) {s t : Set α} : image f s = image f t → s = t := (image_injective f hf).mp
theorem star_104_263 (f : α → β) (s : Set α) {x : α} : s x → image f s (f x) := image_mem f s
theorem star_104_264 (f : α → β) (s : Set α) : nonempty (image f s) ↔ nonempty s := by
  exact ⟨fun ⟨_,x,hx,_⟩ => ⟨x,hx⟩, star_104_211 f⟩
end PM.Architecture.Star104NextKernel
