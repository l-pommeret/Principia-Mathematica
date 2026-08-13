/-! Ordered-section kernel for PM II ✱213, third macro-lot. -/
namespace PM.Architecture.Star213ThirdKernel
abbrev Set (α : Type u) := α → Prop
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def proper (s t : Set α) := subset s t ∧ ∃ x, t x ∧ ¬s x
def comparable (s t : Set α) := subset s t ∨ subset t s
def inter (s t : Set α) : Set α := fun x => s x ∧ t x
def union (s t : Set α) : Set α := fun x => s x ∨ t x

theorem proper_trans {s t u : Set α} : proper s t → proper t u → proper s u := by
 rintro ⟨hst,_⟩ ⟨htu,⟨x,hx,hn⟩⟩
 exact ⟨fun {_} hs => htu (hst hs),⟨x,hx,fun hs => hn (hst hs)⟩⟩
theorem star_213_17 {s t u : Set α} : proper s t → proper t u → proper s u := proper_trans
theorem star_213_171 {s t u : Set α} : proper s t → proper t u → subset s u := fun h k => (proper_trans h k).1
theorem star_213_172 {s t u : Set α} : proper s t → proper t u → s ≠ u := by
 intro h k e; subst u; obtain ⟨x,hx,hn⟩ := (proper_trans h k).2; exact hn hx
theorem star_213_18 {s t : Set α} : proper s t → ∃ x, t x ∧ ¬s x := fun h => h.2
theorem star_213_2 (s t : Set α) : comparable s t ↔ subset s t ∨ subset t s := Iff.rfl
theorem star_213_21 {s t : Set α} : proper s t → comparable s t := fun h => Or.inl h.1
theorem star_213_22 {s t : Set α} : proper s t → ¬proper t s := by
 intro h k; obtain ⟨x,hx,hn⟩ := h.2; exact hn (k.1 hx)
theorem star_213_23 {s t : Set α} : comparable s t → inter s t = s ∨ inter s t = t := by
 rintro (h|h)
 · left; funext x; apply propext; exact ⟨fun q => q.1,fun q => ⟨q,h q⟩⟩
 · right; funext x; apply propext; exact ⟨fun q => q.2,fun q => ⟨h q,q⟩⟩
theorem star_213_24 {s t : Set α} : comparable s t → union s t = t ∨ union s t = s := by
 rintro (h|h)
 · left; funext x; apply propext; exact ⟨fun q => q.elim (fun hs => h hs) id,Or.inr⟩
 · right; funext x; apply propext; exact ⟨fun q => q.elim id (fun ht => h ht),Or.inl⟩
theorem star_213_241 {s t : Set α} : proper s t → subset s t := fun h => h.1
theorem star_213_242 {s t : Set α} : proper s t → comparable s t := star_213_21
theorem star_213_243 {s t : Set α} : proper s t → inter s t = s := by
 intro h; funext x; apply propext
 exact ⟨fun q => q.1,fun hs => ⟨hs,h.1 hs⟩⟩
theorem star_213_244 {s t : Set α} : proper s t → union s t = t := by
 intro h; funext x; apply propext; exact ⟨fun q => q.elim (fun hs => h.1 hs) id,Or.inr⟩
theorem star_213_245 {s t : Set α} : proper s t → s ≠ t := by
 intro h e; subst t; obtain ⟨x,hx,hn⟩ := h.2; exact hn hx
theorem star_213_246 {s t u : Set α} : proper s t → subset t u → subset s u := fun h k {_} hs => k (h.1 hs)
theorem star_213_247 {s t u : Set α} : subset s t → proper t u → subset s u := fun h k {_} hs => k.1 (h hs)
theorem star_213_25 {s t : Set α} : proper s t → ∃ x, t x ∧ ¬s x := fun h => h.2
theorem star_213_251 {s t : Set α} : proper s t → ¬subset t s := by
 intro h k; obtain ⟨x,hx,hn⟩ := h.2; exact hn (k hx)
end PM.Architecture.Star213ThirdKernel
