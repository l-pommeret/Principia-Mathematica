namespace PM.Architecture.Star24Q366Q367Kernel

abbrev Class (α : Sort u) := α → Prop
abbrev Included (a b : Class α) : Prop := ∀ x, a x → b x
abbrev Inter (a b : Class α) : Class α := fun x => a x ∧ b x
abbrev Union (a b : Class α) : Class α := fun x => a x ∨ b x
abbrev Diff (a b : Class α) : Class α := fun x => a x ∧ ¬ b x
abbrev Empty : Class α := fun _ => False
abbrev Universal : Class α := fun _ => True

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x
  exact propext (h x)

/-- PM I ✱24·33. -/
theorem star_24_33 (a b : Class α) : a = Universal → Union a b = Universal := by
  intro ha
  apply class_ext
  intro x
  constructor
  · intro _; trivial
  · intro _; exact Or.inl (by rw [ha]; trivial)

/-- PM I ✱24·34. -/
theorem star_24_34 (a b : Class α) : a = Empty → Inter a b = Empty := by
  intro ha
  apply class_ext
  intro x
  constructor
  · intro h; rw [ha] at h; exact h.1
  · exact False.elim

/-- PM I ✱24·35. -/
theorem star_24_35 (a b : Class α) : a = Universal → Inter a b = b := by
  intro ha
  apply class_ext
  intro x
  constructor
  · exact And.right
  · intro hb; exact ⟨by rw [ha]; trivial, hb⟩

/-- PM I ✱24·36. -/
theorem star_24_36 (a b : Class α) : a = Empty → Union a b = b := by
  intro ha
  apply class_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl hx => rw [ha] at hx; exact False.elim hx
    | inr hb => exact hb
  · exact Or.inr

/-- PM I ✱24·37. -/
theorem star_24_37 (a b : Class α) :
    Inter a b = Empty ↔ ∀ x y, a x → b y → x ≠ y := by
  constructor
  · intro h x y hx hy hxy
    subst y
    have hz : Inter a b x := ⟨hx, hy⟩
    rw [h] at hz
    exact hz
  · intro h
    apply class_ext
    intro x
    constructor
    · intro hx
      exact (h x x hx.1 hx.2) rfl
    · exact False.elim

/-- PM I ✱24·38. -/
theorem star_24_38 (a b : Class α) :
    Inter a b = Empty → a ≠ b ∨ (a = Empty ∧ b = Empty) := by
  intro h
  cases Classical.em (a = b) with
  | inr hab => exact Or.inl hab
  | inl hab =>
      right
      have ha : a = Empty := by
        apply class_ext
        intro x
        constructor
        · intro hx
          have hi : Inter a b x := ⟨hx, hab ▸ hx⟩
          rw [h] at hi
          exact hi
        · exact False.elim
      exact ⟨ha, hab ▸ ha⟩

/-- PM I ✱24·39. -/
theorem star_24_39 (a b : Class α) :
    Inter a b = Empty ↔ ∀ x, a x → ¬ b x := by
  constructor
  · intro h x ha hb
    have hi : Inter a b x := ⟨ha, hb⟩
    rw [h] at hi
    exact hi
  · intro h
    apply class_ext
    intro x
    constructor
    · intro hx; exact h x hx.1 hx.2
    · exact False.elim

/-- PM I ✱24·401. -/
theorem star_24_401 (a b c : Class α) :
    Included b a → Diff (Union b c) a = Diff c a := by
  intro hba
  apply class_ext
  intro x
  constructor
  · intro h
    cases h.1 with
    | inl hb => exact False.elim (h.2 (hba x hb))
    | inr hc => exact ⟨hc, h.2⟩
  · intro h; exact ⟨Or.inr h.1, h.2⟩

/-- PM I ✱24·402. -/
theorem star_24_402 (a b xi eta : Class α) :
    Inter a b = Empty → Included xi a → Included eta b → Inter xi eta = Empty := by
  intro hab hxi heta
  apply class_ext
  intro x
  constructor
  · intro h
    have hi : Inter a b x := ⟨hxi x h.1, heta x h.2⟩
    rw [hab] at hi
    exact hi
  · exact False.elim

end PM.Architecture.Star24Q366Q367Kernel
