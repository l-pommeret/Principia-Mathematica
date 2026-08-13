namespace PM.Architecture.Star24Q369LemmasKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Inter (a b : Class α) : Class α := fun x => a x ∧ b x
abbrev Union (a b : Class α) : Class α := fun x => a x ∨ b x
abbrev Diff (a b : Class α) : Class α := fun x => a x ∧ ¬ b x
abbrev Compl (a : Class α) : Class α := fun x => ¬ a x

/-- The exact printed proposition PM I ✱24·431.

This is retained as a proposition rather than asserted as a theorem: the printed
formula is not valid for classes (see `star_24_431_not_valid` below).
-/
def star_24_431 (a b c : Class α) : Prop :=
  Inter (Union a c) (Union b (Compl c)) =
    Union (Union (Inter a c) (Diff a c)) (Inter b c)

/-- The exact printed ✱24·431 has a one-point counterexample. -/
theorem star_24_431_not_valid :
    ¬ ∀ (a b c : Class Unit), star_24_431 a b c := by
  intro h
  have eq := h (fun _ => True) (fun _ => False) (fun _ => True)
  have rhs :
      Union
          (Union
            (Inter (fun _ : Unit => True) (fun _ : Unit => True))
            (Diff (fun _ : Unit => True) (fun _ : Unit => True)))
          (Inter (fun _ : Unit => False) (fun _ : Unit => True)) () :=
    Or.inl (Or.inl ⟨True.intro, True.intro⟩)
  rw [← eq] at rhs
  exact rhs.2.elim (fun hf => hf) (fun hn => hn True.intro)

/-- PM I ✱24·432. -/
theorem star_24_432 (a b c : Class α) :
    Union (Diff a c) (Inter b c) =
      Union (Union (Inter a b) (Diff a c)) (Inter b c) := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.elim (fun hac => Or.inl (Or.inr hac)) Or.inr
  · intro h
    cases h with
    | inl h =>
        cases h with
        | inl hab =>
            by_cases hc : c x
            · exact Or.inr ⟨hab.2, hc⟩
            · exact Or.inl ⟨hab.1, hc⟩
        | inr hac => exact Or.inl hac
    | inr hbc => exact Or.inr hbc

end PM.Architecture.Star24Q369LemmasKernel
