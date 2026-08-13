namespace PM.Architecture.Star43OpeningKernel

abbrev Relation (α : Type u) := α → α → Prop

def product (R S : Relation α) : Relation α :=
  fun x z => ∃ y, R x y ∧ S y z

def leftProduct (R : Relation α) (P Q : Relation α) : Prop :=
  P = product R Q

def rightProduct (R : Relation α) (P Q : Relation α) : Prop :=
  P = product Q R

def sandwich (R S : Relation α) (P Q : Relation α) : Prop :=
  P = product (product R Q) S

private def uniqueValue
    (F : Relation α → Relation α → Prop) (Q : Relation α) : Prop :=
  ∃ P, F P Q ∧ ∀ T, F T Q → T = P

private theorem product_assoc (R S Q : Relation α) :
    product (product R S) Q = product R (product S Q) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨w, ⟨y, hR, hS⟩, hQ⟩
    exact ⟨y, hR, w, hS, hQ⟩
  · rintro ⟨y, hR, w, hS, hQ⟩
    exact ⟨w, ⟨y, hR, hS⟩, hQ⟩

/-- ✱43·1. -/
theorem star_43_1 (P Q R : Relation α) :
    leftProduct R P Q ↔ P = product R Q := Iff.rfl

/-- ✱43·101. -/
theorem star_43_101 (P Q R : Relation α) :
    rightProduct R P Q ↔ P = product Q R := Iff.rfl

/-- ✱43·102. -/
theorem star_43_102 (P Q R S : Relation α) :
    sandwich R S P Q ↔ P = product (product R Q) S := Iff.rfl

/-- ✱43·11. -/
theorem star_43_11 (R Q : Relation α) :
    product R Q = product R Q := rfl

/-- ✱43·111. -/
theorem star_43_111 (R Q : Relation α) :
    product Q R = product Q R := rfl

/-- ✱43·112. -/
theorem star_43_112 (R Q S : Relation α) :
    product (product R Q) S = product (product R Q) S := rfl

/-- ✱43·12. -/
theorem star_43_12 (R Q : Relation α) : uniqueValue (leftProduct R) Q := by
  refine ⟨product R Q, rfl, ?_⟩
  intro T h
  exact h

/-- ✱43·121. -/
theorem star_43_121 (R Q : Relation α) : uniqueValue (rightProduct R) Q := by
  refine ⟨product Q R, rfl, ?_⟩
  intro T h
  exact h

/-- ✱43·122. -/
theorem star_43_122 (R Q S : Relation α) :
    uniqueValue (sandwich R S) Q := by
  refine ⟨product (product R Q) S, rfl, ?_⟩
  intro T h
  exact h

/-- ✱43·2. `(R|)|(S|) = (R|S)|`. -/
theorem star_43_2 (R S : Relation α) :
    (fun P Q => ∃ T, leftProduct R P T ∧ leftProduct S T Q) =
      leftProduct (product R S) := by
  funext P Q
  apply propext
  constructor
  · rintro ⟨T, rfl, rfl⟩
    exact (product_assoc R S Q).symm
  · intro h
    refine ⟨product S Q, ?_, rfl⟩
    exact h.trans (product_assoc R S Q)

end PM.Architecture.Star43OpeningKernel
