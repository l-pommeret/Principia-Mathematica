/-! Nested-section kernel for PM II ✱213, fourth macro-lot. -/
namespace PM.Architecture.Star213FourthKernel
abbrev Set (α : Type u) := α → Prop
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def proper (s t : Set α) := subset s t ∧ ∃ x, t x ∧ ¬s x
def diff (s t : Set α) : Set α := fun x => s x ∧ ¬t x
def inter (s t : Set α) : Set α := fun x => s x ∧ t x
def nonempty (s : Set α) := ∃ x, s x
def disjoint (s t : Set α) := ∀ x, s x → t x → False

theorem star_213_3 {s t : Set α} : proper s t → nonempty (diff t s) := fun h => h.2
theorem star_213_301 {s t : Set α} : proper s t → subset s t := fun h => h.1
theorem star_213_302 {s t : Set α} : proper s t → ¬subset t s := by
 intro h k; obtain ⟨x,hx,hn⟩ := h.2; exact hn (k hx)
theorem star_213_31 {s t : Set α} : proper s t → s ≠ t := by
 intro h e; subst t; obtain ⟨x,hx,hn⟩ := h.2; exact hn hx
theorem star_213_32 {s t : Set α} : proper s t → nonempty t := by
 intro h; obtain ⟨x,hx,_⟩ := h.2; exact ⟨x,hx⟩
theorem star_213_4 (s : Set α) : inter s s = s := by funext x; apply propext; exact ⟨fun h => h.1,fun h => ⟨h,h⟩⟩
theorem star_213_41 {s t : Set α} (h : subset s t) : inter s t = s := by funext x; apply propext; exact ⟨fun q => q.1,fun q => ⟨q,h q⟩⟩
theorem star_213_42 {s t : Set α} (h : subset t s) : inter s t = t := by funext x; apply propext; exact ⟨fun q => q.2,fun q => ⟨h q,q⟩⟩
theorem star_213_5 {s t : Set α} (h : proper s t) : nonempty (diff t s) := h.2
theorem star_213_51 {s t : Set α} (h : proper s t) : disjoint s (diff t s) := fun x hs hd => hd.2 hs
theorem star_213_52 {s t : Set α} (h : proper s t) : subset (diff t s) t := fun {_} hd => hd.1
theorem star_213_53 {s t : Set α} (h : proper s t) : ¬subset (diff t s) s := by
 intro k; obtain ⟨x,hx,hn⟩ := h.2; exact hn (k ⟨hx,hn⟩)
theorem star_213_531 {s t : Set α} (h : proper s t) : nonempty (diff t s) := h.2
theorem star_213_54 {s t u : Set α} (h : subset s t) (k : subset t u) : subset s u := fun {_} hs => k (h hs)
theorem star_213_541 {s t u : Set α} (h : proper s t) (k : proper t u) : proper s u := by
 refine ⟨star_213_54 h.1 k.1,?_⟩
 obtain ⟨x,hx,hn⟩ := k.2; exact ⟨x,hx,fun hs => hn (h.1 hs)⟩
theorem star_213_55 {s t u : Set α} (h : proper s t) (k : proper t u) : subset (diff t s) u := fun {_} hx => k.1 hx.1
theorem star_213_56 {s t u : Set α} (h : proper s t) (k : proper t u) : disjoint (diff t s) (diff u t) := fun x hx hy => hy.2 hx.1
theorem star_213_561 {s t u : Set α} (h : proper s t) (k : proper t u) : nonempty (diff u s) := (star_213_541 h k).2
end PM.Architecture.Star213FourthKernel
