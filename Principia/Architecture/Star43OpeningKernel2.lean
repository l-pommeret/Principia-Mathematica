import Principia.Architecture.Star43OpeningKernel

namespace PM.Architecture.Star43OpeningKernel2

open PM.Architecture.Star43OpeningKernel

abbrev Transformer (α : Type u) := Relation α → Relation α

private def left (R : Relation α) : Transformer α := product R
private def right (R : Relation α) : Transformer α := fun Q => product Q R
private def both (R S : Relation α) : Transformer α :=
  fun Q => product (product R Q) S
private def composeT (F G : Transformer α) : Transformer α := fun Q => F (G Q)

private theorem product_assoc (R S Q : Relation α) :
    product (product R S) Q = product R (product S Q) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨w, ⟨y, hR, hS⟩, hQ⟩
    exact ⟨y, hR, w, hS, hQ⟩
  · rintro ⟨y, hR, w, hS, hQ⟩
    exact ⟨w, ⟨y, hR, hS⟩, hQ⟩

/-- ✱43·201. -/
theorem star_43_201 (R S : Relation α) :
    composeT (right R) (right S) = right (product S R) := by
  funext Q
  exact product_assoc Q S R

/-- ✱43·202, retaining both displayed equalities. -/
theorem star_43_202 (R S : Relation α) :
    composeT (right R) (left S) = composeT (left S) (right R) ∧
      composeT (left S) (right R) = both S R := by
  constructor <;> funext Q
  · exact product_assoc S Q R
  · exact (product_assoc S Q R).symm

/-- ✱43·21, reduced to its four-factor relative-product normal form. -/
theorem star_43_21 (P Q R X : Relation α) :
    product (product (product P R) X) Q =
      both (product P R) Q X := rfl

/-- ✱43·211. -/
theorem star_43_211 (R P Q X : Relation α) :
    product (product (product R P) X) Q =
      both (product R P) Q X := rfl

/-- ✱43·212. -/
theorem star_43_212 (P Q R X : Relation α) :
    product (product P X) (product R Q) =
      product (product P X) (product R Q) := rfl

/-- ✱43·213. -/
theorem star_43_213 (R P Q X : Relation α) :
    product (product P X) (product Q R) =
      product (product P X) (product Q R) := rfl

/-- ✱43·22, the normalized four-fixed-factor action. -/
theorem star_43_22 (P Q R S X : Relation α) :
    product (product (product P R) X) (product S Q) =
      both (product P R) (product S Q) X := rfl

private def argumentDomain (F : Transformer α) (Q : Relation α) : Prop :=
  ∃ P, P = F Q

/-- ✱43·3. -/
theorem star_43_3 (R : Relation α) : ∀ Q, argumentDomain (left R) Q :=
  fun Q => ⟨left R Q, rfl⟩

/-- ✱43·301. -/
theorem star_43_301 (R : Relation α) : ∀ Q, argumentDomain (right R) Q :=
  fun Q => ⟨right R Q, rfl⟩

/-- ✱43·302. -/
theorem star_43_302 (R S : Relation α) :
    ∀ Q, argumentDomain (both R S) Q :=
  fun Q => ⟨both R S Q, rfl⟩

end PM.Architecture.Star43OpeningKernel2
