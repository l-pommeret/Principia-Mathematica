namespace PM.Architecture.Star24Q368Q369Kernel

abbrev Class (α : Sort u) := α → Prop
abbrev Included (a b : Class α) : Prop := ∀ x, a x → b x
abbrev Inter (a b : Class α) : Class α := fun x => a x ∧ b x
abbrev Union (a b : Class α) : Class α := fun x => a x ∨ b x
abbrev Diff (a b : Class α) : Class α := fun x => a x ∧ ¬ b x
abbrev Compl (a : Class α) : Class α := fun x => ¬ a x
abbrev Empty : Class α := fun _ => False

/-- PM I ✱24·41. -/
theorem star_24_41 (a b : Class α) : a = Union (Inter a b) (Diff a b) := by
  funext x
  apply propext
  constructor
  · intro ha
    by_cases hb : b x
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · intro h
    exact h.elim And.left And.left

/-- PM I ✱24·411. -/
theorem star_24_411 (a b : Class α) :
    Included b a → a = Union b (Diff a b) := by
  intro hba
  funext x
  apply propext
  constructor
  · intro ha
    by_cases hb : b x
    · exact Or.inl hb
    · exact Or.inr ⟨ha, hb⟩
  · intro h
    exact h.elim (hba x) And.left

/-- PM I ✱24·412. -/
theorem star_24_412 (a b c : Class α) :
    Included b a → Included c b → Union (Diff a b) (Diff b c) = Diff a c := by
  intro hba hcb
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl h => exact ⟨h.1, fun hc => h.2 (hcb x hc)⟩
    | inr h => exact ⟨hba x h.1, h.2⟩
  · intro h
    by_cases hb : b x
    · exact Or.inr ⟨hb, h.2⟩
    · exact Or.inl ⟨h.1, hb⟩

/-- PM I ✱24·42. -/
theorem star_24_42 (a b c : Class α) :
    (Included (Inter a b) c ∧ Included (Diff a b) c) ↔ Included a c := by
  constructor
  · intro h x ha
    by_cases hb : b x
    · exact h.1 x ⟨ha, hb⟩
    · exact h.2 x ⟨ha, hb⟩
  · intro h
    exact ⟨fun x hx => h x hx.1, fun x hx => h x hx.1⟩

/-- PM I ✱24·43. -/
theorem star_24_43 (a b c : Class α) :
    Included (Diff a b) c ↔ Included a (Union b c) := by
  constructor
  · intro h x ha
    by_cases hb : b x
    · exact Or.inl hb
    · exact Or.inr (h x ⟨ha, hb⟩)
  · intro h x hx
    cases h x hx.1 with
    | inl hb => exact False.elim (hx.2 hb)
    | inr hc => exact hc

/-- PM I ✱24·44. -/
theorem star_24_44 (a b c : Class α) :
    Inter (Union a c) (Union b (Compl c)) =
      Union (Inter a (Compl c)) (Inter b c) := by
  funext x
  apply propext
  constructor
  · intro h
    by_cases hc : c x
    · exact Or.inr ⟨h.2.resolve_right (fun hnc => hnc hc), hc⟩
    · exact Or.inl ⟨h.1.resolve_right hc, hc⟩
  · intro h
    cases h with
    | inl h => exact ⟨Or.inl h.1, Or.inr h.2⟩
    | inr h => exact ⟨Or.inr h.2, Or.inl h.1⟩

/-- PM I ✱24·45. -/
theorem star_24_45 (a b c : Class α) :
    Union (Inter a c) (Diff b c) = Empty ↔
      Included b c ∧ Included c (Compl a) := by
  constructor
  · intro h
    constructor
    · intro x hb
      cases Classical.em (c x) with
      | inl hc => exact hc
      | inr hnc =>
          have hx : Union (Inter a c) (Diff b c) x := Or.inr ⟨hb, hnc⟩
          rw [h] at hx
          exact False.elim hx
    · intro x hc
      intro ha
      have hx : Union (Inter a c) (Diff b c) x := Or.inl ⟨ha, hc⟩
      rw [h] at hx
      exact hx
  · intro h
    funext x
    apply propext
    constructor
    · intro hx
      cases hx with
      | inl hx => exact h.2 x hx.2 hx.1
      | inr hx => exact hx.2 (h.1 x hx.1)
    · exact False.elim

/-- PM I ✱24·46. -/
theorem star_24_46 (a b c : Class α) :
    Union (Inter a c) (Diff b c) = Empty → Inter a b = Empty := by
  intro h
  funext x
  apply propext
  constructor
  · intro hx
    by_cases hc : c x
    · have : Union (Inter a c) (Diff b c) x := Or.inl ⟨hx.1, hc⟩
      rw [h] at this
      exact this
    · have : Union (Inter a c) (Diff b c) x := Or.inr ⟨hx.2, hc⟩
      rw [h] at this
      exact this
  · exact False.elim

end PM.Architecture.Star24Q368Q369Kernel
