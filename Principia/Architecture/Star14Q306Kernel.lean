/-!
# PM I, ✱14·171, ✱14·2, ✱14·201, ✱14·203

Exact contextual-description readings.  A description is never made a term:
`DescriptionEquals φ b` is precisely the ✱14·01 expansion
`∀ x, φ x ↔ x = b`, and description application remains scoped.
-/

namespace PM.Architecture.Star14Q306Kernel

def DescriptionEquals {α : Sort _} (φ : α → Prop) (b : α) : Prop :=
  ∀ x, φ x ↔ x = b

def DescriptionExists {α : Sort _} (φ : α → Prop) : Prop :=
  ∃ b, DescriptionEquals φ b

def DescriptionScope {α : Sort _} (φ ψ : α → Prop) : Prop :=
  ∃ b, DescriptionEquals φ b ∧ ψ b

/-- ✱14·171. Description identity is Leibniz substitution into every
predicative matrix, with the description occurrence kept contextually scoped. -/
theorem star_14_171 {α : Sort _} (φ : α → Prop) (b : α) :
    DescriptionEquals φ b ↔
      ∀ ψ : α → Prop, ψ b → DescriptionScope φ ψ := by
  constructor
  · intro h ψ hψ
    exact ⟨b, h, hψ⟩
  · intro h
    obtain ⟨c, hc, hcb⟩ := h (fun x => x = b) rfl
    simpa [hcb] using hc

/-- ✱14·2. The description of objects identical with `a` is identical
with `a`, expressed without introducing a description-valued term. -/
theorem star_14_2 {α : Sort _} (a : α) :
    DescriptionEquals (fun x => x = a) a := by
  intro x
  exact Iff.rfl

/-- ✱14·201. Description existence entails ordinary existence. -/
theorem star_14_201 {α : Sort _} (φ : α → Prop) :
    DescriptionExists φ → ∃ x, φ x := by
  rintro ⟨b, hb⟩
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱14·203. Description existence is exactly existence plus uniqueness. -/
theorem star_14_203 {α : Sort _} (φ : α → Prop) :
    DescriptionExists φ ↔
      ((∃ x, φ x) ∧ ∀ x y, φ x → φ y → x = y) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, (hb b).2 rfl⟩, ?_⟩
    intro x y hx hy
    exact (hb x).mp hx |>.trans ((hb y).mp hy).symm
  · rintro ⟨⟨b, hb⟩, unique⟩
    refine ⟨b, fun x => ⟨fun hx => unique x b hx hb, ?_⟩⟩
    rintro rfl
    exact hb

end PM.Architecture.Star14Q306Kernel
