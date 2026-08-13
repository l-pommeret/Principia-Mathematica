namespace PM.Architecture.Star24Q367Kernel

private abbrev Class (ι : Type u) := ι → Prop
private def empty : Class ι := fun _ => False
private def inter (α β : Class ι) : Class ι := fun x => α x ∧ β x
private def union (α β : Class ι) : Class ι := fun x => α x ∨ β x
private def diff (α β : Class ι) : Class ι := fun x => α x ∧ ¬ β x
private def subset (α β : Class ι) : Prop := ∀ x, α x → β x

theorem star_24_38 (α β : Class ι) :
    inter α β = empty → α ≠ β ∨ (α = empty ∧ β = empty) := by
  intro disjoint
  by_cases hab : α = β
  · right
    subst β
    have ha : α = empty := by
      funext x
      apply propext
      constructor
      · intro hx
        have h : inter α α x := ⟨hx, hx⟩
        rw [disjoint] at h
        exact h
      · exact False.elim
    exact ⟨ha, ha⟩
  · exact Or.inl hab

theorem star_24_39 (α β : Class ι) :
    inter α β = empty ↔ ∀ x, α x → ¬ β x := by
  constructor
  · intro h x hx hβ
    have hab : inter α β x := ⟨hx, hβ⟩
    rw [h] at hab
    exact hab
  · intro h
    funext x
    apply propext
    exact ⟨fun hx => (h x hx.1 hx.2).elim, False.elim⟩

theorem star_24_4 (α β : Class ι) :
    ((inter α β = empty) ↔ diff (union α β) α = β) ∧
      ((diff (union α β) α = β) ↔ diff (union α β) β = α) := by
  have left : inter α β = empty ↔ diff (union α β) α = β := by
    constructor
    · intro h
      funext x
      apply propext
      constructor
      · rintro ⟨ha | hb, hna⟩
        · exact (hna ha).elim
        · exact hb
      · intro hb
        refine ⟨Or.inr hb, ?_⟩
        intro ha
        have hab : inter α β x := ⟨ha, hb⟩
        rw [h] at hab
        exact hab
    · intro h
      apply (star_24_39 α β).2
      intro x ha hb
      have hd : diff (union α β) α x := by rw [h]; exact hb
      exact hd.2 ha
  have right : inter α β = empty ↔ diff (union α β) β = α := by
    constructor
    · intro h
      funext x
      apply propext
      constructor
      · rintro ⟨ha | hb, hnb⟩
        · exact ha
        · exact (hnb hb).elim
      · intro ha
        exact ⟨Or.inl ha, (star_24_39 α β).1 h x ha⟩
    · intro h
      apply (star_24_39 α β).2
      intro x ha hb
      have hd : diff (union α β) β x := by rw [h]; exact ha
      exact hd.2 hb
  exact ⟨left, left.symm.trans right⟩

theorem star_24_401 (α β γ : Class ι) :
    subset β α → diff (union β γ) α = diff γ α := by
  intro h
  funext x
  apply propext
  constructor
  · rintro ⟨hb | hg, hna⟩
    · exact (hna (h x hb)).elim
    · exact ⟨hg, hna⟩
  · rintro ⟨hg, hna⟩
    exact ⟨Or.inr hg, hna⟩

theorem star_24_402 (α β ξ η : Class ι) :
    inter α β = empty → subset ξ α → subset η β → inter ξ η = empty := by
  intro hab hξ hη
  apply (star_24_39 ξ η).2
  intro x hx hy
  exact (star_24_39 α β).1 hab x (hξ x hx) (hη x hy)

end PM.Architecture.Star24Q367Kernel
