namespace PM.Architecture.Star22Q344Kernel

universe u

/-- The explicit simple-type carrier of a PM class extension. -/
abbrev ClassExtension (α : Sort u) := α → Prop

/-- PM I ✱22·01, used transparently by both Q344 propositions. -/
abbrev Included (A B : ClassExtension α) : Prop :=
  ∀ x, A x → B x

/-- PM I ✱22·44: inclusion is transitive. -/
theorem star_22_44 (A B C : ClassExtension α) :
    Included A B → Included B C → Included A C := by
  intro hAB hBC x hx
  exact hBC x (hAB x hx)

/-- PM I ✱22·441: inclusion eliminates at the displayed member. -/
theorem star_22_441 (A B : ClassExtension α) (x : α) :
    Included A B → A x → B x := by
  intro hAB hx
  exact hAB x hx

end PM.Architecture.Star22Q344Kernel
