/-! Inclusion kernel for consecutive segments in PM II ✱213. -/
namespace PM.Architecture.Star213Kernel
abbrev Set (α : Type u) := α → Prop
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def proper (s t : Set α) := subset s t ∧ ∃ x, t x ∧ ¬s x
def empty : Set α := fun _ => False
def SegmentStep (s t : Set α) : Prop := proper s t
def comparable (s t : Set α) : Prop := subset s t ∨ subset t s

theorem star_213_01 (s t : Set α) : SegmentStep s t ↔ proper s t := Iff.rfl
theorem star_213_1 (s t : Set α) : SegmentStep s t ↔ subset s t ∧ ∃ x, t x ∧ ¬s x := Iff.rfl
theorem star_213_11 (s t : Set α) : SegmentStep s t → subset s t := fun h => h.1
theorem star_213_12 (s t : Set α) : SegmentStep s t → ¬subset t s := by
 rintro h hts
 obtain ⟨x,hx,hn⟩ := h.2
 exact hn (hts hx)
theorem star_213_121 (s t : Set α) : SegmentStep s t → s ≠ t := by
 intro h e; subst t; exact star_213_12 s s h (fun {_} hx => hx)
theorem star_213_122 (s t : Set α) : SegmentStep s t → ∃ x, t x ∧ ¬s x := by
 intro h; exact h.2
theorem star_213_123 (s t : Set α) : SegmentStep s t → comparable s t := fun h => Or.inl h.1
theorem star_213_124 (s t : Set α) : SegmentStep s t → ¬SegmentStep t s := by
 intro h k; exact (star_213_12 s t h) k.1
theorem star_213_125 (s t u : Set α) : SegmentStep s t → SegmentStep t u → subset s u :=
 fun h k {_} hx => k.1 (h.1 hx)
theorem star_213_126 (s t u : Set α) : SegmentStep s t → SegmentStep t u → SegmentStep s u := by
 intro h k; refine ⟨star_213_125 s t u h k,?_⟩
 obtain ⟨x,hx,hn⟩ := k.2
 exact ⟨x,hx,fun hs => hn (h.1 hs)⟩
theorem star_213_13 (s : Set α) : ¬SegmentStep s s := fun h => (star_213_12 s s h) (fun {_} hx => hx)
theorem star_213_131 (s t : Set α) : SegmentStep s t → ¬SegmentStep t s := star_213_124 s t
theorem star_213_132 (s t u : Set α) : SegmentStep s t → SegmentStep t u → SegmentStep s u := star_213_126 s t u
theorem star_213_133 (s t u : Set α) : SegmentStep s t → subset t u → subset s u := fun h k {_} hx => k (h.1 hx)
theorem star_213_134 (s t u : Set α) : subset s t → SegmentStep t u → subset s u := fun h k {_} hx => k.1 (h hx)
theorem star_213_14 (s t : Set α) : SegmentStep s t → ∃ x, t x ∧ ¬s x := star_213_122 s t
theorem star_213_141 (s t : Set α) : SegmentStep s t → s ≠ t := star_213_121 s t
theorem star_213_142 (s t : Set α) : SegmentStep s t → comparable s t := star_213_123 s t
end PM.Architecture.Star213Kernel
