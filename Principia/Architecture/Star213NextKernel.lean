/-! Chain-of-segments kernel for PM II ✱213, second macro-lot. -/
namespace PM.Architecture.Star213NextKernel
abbrev Set (α : Type u) := α → Prop
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def proper (s t : Set α) := subset s t ∧ ∃ x, t x ∧ ¬s x
def union (s t : Set α) : Set α := fun x => s x ∨ t x
def inter (s t : Set α) : Set α := fun x => s x ∧ t x
def diff (s t : Set α) : Set α := fun x => s x ∧ ¬t x
def comparable (s t : Set α) := subset s t ∨ subset t s

theorem star_213_143 (s t : Set α) (h : proper s t) : subset s t := h.1
theorem star_213_144 (s t : Set α) (h : proper s t) : ∃ x, t x ∧ ¬s x := h.2
theorem star_213_145 (s t : Set α) (h : proper s t) : comparable s t := Or.inl h.1
theorem star_213_146 (s t : Set α) (h : proper s t) : s ≠ t := by
 intro e; subst t; obtain ⟨x,hx,hn⟩ := h.2; exact hn hx
theorem star_213_15 (s t : Set α) (h : subset s t) : inter s t = s := by
 funext x; apply propext; exact ⟨fun q => q.1, fun q => ⟨q,h q⟩⟩
theorem star_213_151 (s t : Set α) (h : subset s t) : union s t = t := by
 funext x; apply propext; exact ⟨fun q => q.elim (fun hs => h hs) id, Or.inr⟩
theorem star_213_152 (s t : Set α) (h : proper s t) : inter s t = s := star_213_15 s t h.1
theorem star_213_153 (s t : Set α) (h : proper s t) : union s t = t := star_213_151 s t h.1
theorem star_213_154 (s t : Set α) (h : proper s t) : ∃ x, diff t s x := h.2
theorem star_213_155 (s t : Set α) (h : proper s t) : ∀ ⦃x⦄, s x → ¬diff t s x := fun {_} hs hd => hd.2 hs
theorem star_213_156 (s t u : Set α) (h : subset s t) (k : subset t u) : subset s u := fun {_} hx => k (h hx)
theorem star_213_157 (s t u : Set α) (h : proper s t) (k : proper t u) : proper s u := by
 refine ⟨star_213_156 s t u h.1 k.1,?_⟩
 obtain ⟨x,hx,hn⟩ := k.2; exact ⟨x,hx,fun hs => hn (h.1 hs)⟩
theorem star_213_158 (s t : Set α) (h : proper s t) : ¬proper t s := by
 intro k; obtain ⟨x,hx,hn⟩ := h.2; exact hn (k.1 hx)
theorem star_213_16 (s : Set α) : subset s s := fun {_} h => h
theorem star_213_161 (s : Set α) : ¬proper s s := by
 intro h; obtain ⟨x,hx,hn⟩ := h.2; exact hn hx
theorem star_213_162 (s t : Set α) : proper s t → subset s t := fun h => h.1
theorem star_213_163 (s t : Set α) : proper s t → ¬subset t s := by
 intro h hts; obtain ⟨x,hx,hn⟩ := h.2; exact hn (hts hx)
theorem star_213_164 (s t : Set α) : proper s t → ¬proper t s := star_213_158 s t
end PM.Architecture.Star213NextKernel
