namespace PM.Architecture.Star22Q358Kernel

universe u


abbrev ClassExtension (α : Sort u) := α → Prop

private def union (A B : ClassExtension α) : ClassExtension α :=
  fun x => A x ∨ B x

private def inter (A B : ClassExtension α) : ClassExtension α :=
  fun x => A x ∧ B x

private def diff (A B : ClassExtension α) : ClassExtension α :=
  fun x => A x ∧ ¬ B x

private def Included (A B : ClassExtension α) : Prop :=
  ∀ x, A x → B x

private theorem classExt {A B : ClassExtension α} (h : ∀ x, A x ↔ B x) :
    A = B := by
  funext x
  exact propext (h x)

/-- PM I ✱22·89. -/
theorem star_22_89 (A : ClassExtension α) :
    ∀ x, ¬ diff A A x := by
  intro x h
  exact h.2 h.1

/-- PM I ✱22·9. -/
theorem star_22_9 (A B : ClassExtension α) :
    diff (union A B) B = diff A B := by
  apply classExt
  intro x
  constructor
  · rintro ⟨hA | hB, hnB⟩
    · exact ⟨hA, hnB⟩
    · exact False.elim (hnB hB)
  · rintro ⟨hA, hnB⟩
    exact ⟨Or.inl hA, hnB⟩

/-- PM I ✱22·91.  This is the one classically valid Boolean decomposition in
the batch; excluded middle is used only for membership in `A`. -/
theorem star_22_91 (A B : ClassExtension α) :
    union A B = union A (diff B A) := by
  apply classExt
  intro x
  constructor
  · intro h
    rcases h with hA | hB
    · exact Or.inl hA
    · by_cases hA : A x
      · exact Or.inl hA
      · exact Or.inr ⟨hB, hA⟩
  · rintro (hA | ⟨hB, _⟩)
    · exact Or.inl hA
    · exact Or.inr hB

/-- PM I ✱22·92. -/
theorem star_22_92 (A B : ClassExtension α) :
    Included A B → B = union A (diff B A) := by
  intro hAB
  apply classExt
  intro x
  constructor
  · intro hB
    by_cases hA : A x
    · exact Or.inl hA
    · exact Or.inr ⟨hB, hA⟩
  · rintro (hA | ⟨hB, _⟩)
    · exact hAB x hA
    · exact hB

/-- PM I ✱22·93. -/
theorem star_22_93 (A B : ClassExtension α) :
    diff A B = diff A (inter A B) := by
  apply classExt
  intro x
  constructor
  · rintro ⟨hA, hnB⟩
    exact ⟨hA, fun h => hnB h.2⟩
  · rintro ⟨hA, hnInter⟩
    exact ⟨hA, fun hB => hnInter ⟨hA, hB⟩⟩

end PM.Architecture.Star22Q358Kernel
