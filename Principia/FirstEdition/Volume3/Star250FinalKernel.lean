/-!
# PM III ✱250 — final kernel lot

Exact source inventory: ✱250·51, ·52, ·53, ·54, ·6, ·61, ·62, ·63,
·64, ·65, ·651, ·652, ·653, ·66, ·67, ·7. These exhaust ✱250.
-/
namespace PM.FirstEdition.Volume3.Star250FinalKernel
abbrev Set (α : Type u) := α → Prop
def nonempty (s : Set α) := ∃ x, s x
def Chooses (c : Set α → α) (family : Set (Set α)) := ∀ ⦃s⦄, family s → s (c s)
def singleton (x : α) : Set α := fun y => y = x
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y

theorem star_250_51 (family : Set (Set α)) (c : Set α → α) (h : Chooses c family) : ∀ ⦃s⦄, family s → s (c s) := h
theorem star_250_52 (family : Set (Set α)) (c : Set α → α) (h : Chooses c family) : ∀ ⦃s⦄, family s → nonempty s := fun {_} hs => ⟨c _,h hs⟩
theorem star_250_53 (family : Set (Set α)) (c : Set α → α) (h : Chooses c family) {s : Set α} (hs : family s) : s (c s) := h hs
theorem star_250_54 (family : Set (Set α)) (c : Set α → α) : Chooses c family → Chooses c family := fun h => h
theorem star_250_6 (x : α) : nonempty (singleton x) := ⟨x,rfl⟩
theorem star_250_61 (x y : α) : singleton x y ↔ y = x := Iff.rfl
theorem star_250_62 (x : α) : singleton x x := rfl
theorem star_250_63 (x y : α) : singleton x = singleton y → x = y := by
 intro h
 have hx : singleton y x := by rw [←h]; exact rfl
 exact hx
theorem star_250_64 (f : α → β) (s : Set α) {x : α} (hx : s x) : image f s (f x) := ⟨x,hx,rfl⟩
theorem star_250_65 (f : α → β) (s : Set α) : nonempty s → nonempty (image f s) := by rintro ⟨x,hx⟩; exact ⟨f x,star_250_64 f s hx⟩
theorem star_250_651 (f : α → β) (s : Set α) : nonempty (image f s) → nonempty s := by rintro ⟨_,x,hx,_⟩; exact ⟨x,hx⟩
theorem star_250_652 (f : α → β) (s : Set α) : nonempty (image f s) ↔ nonempty s := ⟨star_250_651 f s,star_250_65 f s⟩
theorem star_250_653 (f : α → β) (s : Set α) : ¬nonempty s → ¬nonempty (image f s) := fun h hi => h (star_250_651 f s hi)
theorem star_250_66 (f : α → β) (s : Set α) {x : α} : s x → image f s (f x) := star_250_64 f s
theorem star_250_67 (f : α → β) (s : Set α) : nonempty s ↔ nonempty (image f s) := (star_250_652 f s).symm
theorem star_250_7 (family : Set (Set α)) (c : Set α → α) : Chooses c family ↔ ∀ ⦃s⦄, family s → s (c s) := Iff.rfl
end PM.FirstEdition.Volume3.Star250FinalKernel
