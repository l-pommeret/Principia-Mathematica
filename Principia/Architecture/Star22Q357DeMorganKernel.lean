/-!
# PM I ✱22·84–88

Exact typed-class De Morgan and excluded-middle laws. Class operations are
defined pointwise on one fixed member type.
-/

namespace PM.Architecture.Star22Q357DeMorganKernel

abbrev TypedClass (α : Sort _) := α → Prop

def inter (a b : TypedClass α) : TypedClass α := fun x => a x ∧ b x
def union (a b : TypedClass α) : TypedClass α := fun x => a x ∨ b x
def compl (a : TypedClass α) : TypedClass α := fun x => ¬ a x

/-- ✱22·84. The complement of an intersection is the union of the
complements. -/
theorem star_22_84 (a b : TypedClass α) :
    compl (inter a b) = union (compl a) (compl b) := by
  funext x
  apply propext
  constructor
  · intro h
    by_cases ha : a x
    · exact Or.inr (fun hb => h ⟨ha, hb⟩)
    · exact Or.inl ha
  · intro h hab
    exact h.elim (fun ha => ha hab.1) (fun hb => hb hab.2)

/-- ✱22·85. An intersection is the complement of the union of the
complements. -/
theorem star_22_85 (a b : TypedClass α) :
    inter a b = compl (union (compl a) (compl b)) := by
  funext x
  apply propext
  constructor
  · rintro ⟨ha, hb⟩ h
    exact h.elim (fun hna => hna ha) (fun hnb => hnb hb)
  · intro h
    constructor
    · exact Classical.byContradiction fun hna => h (Or.inl hna)
    · exact Classical.byContradiction fun hnb => h (Or.inr hnb)

/-- ✱22·86. The complement of the intersection of two complements is their
union. -/
theorem star_22_86 (a b : TypedClass α) :
    compl (inter (compl a) (compl b)) = union a b := by
  funext x
  apply propext
  constructor
  · intro h
    by_cases ha : a x
    · exact Or.inl ha
    · exact Or.inr (Classical.byContradiction fun hb => h ⟨ha, hb⟩)
  · intro h hn
    exact h.elim (fun ha => hn.1 ha) (fun hb => hn.2 hb)

/-- ✱22·87. The intersection of two complements is the complement of their
union. -/
theorem star_22_87 (a b : TypedClass α) :
    inter (compl a) (compl b) = compl (union a b) := by
  funext x
  apply propext
  constructor
  · rintro ⟨hna, hnb⟩ h
    exact h.elim hna hnb
  · intro h
    exact ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩

/-- ✱22·88. Every possible object belongs to a class or its complement. -/
theorem star_22_88 (a : TypedClass α) :
    ∀ x, union a (compl a) x := by
  intro x
  exact Classical.em (a x)

end PM.Architecture.Star22Q357DeMorganKernel
