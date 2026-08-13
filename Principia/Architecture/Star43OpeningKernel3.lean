import Principia.Architecture.Star43OpeningKernel

namespace PM.Architecture.Star43OpeningKernel3

open PM.Architecture.Star43OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev Transformer (α : Type u) := Relation α → Relation α

private def left (R : Relation α) : Transformer α := product R
private def right (R : Relation α) : Transformer α := fun P => product P R
private def both (R S : Relation α) : Transformer α := fun P => product (product R P) S
private def fullDomain (_ : Transformer α) (_ : Relation α) : Prop := True
private def restrictT (F : Transformer α) (D : Relation α → Prop) : Transformer α :=
  fun P x y => F P x y ∧ D P

private theorem restrict_full (F : Transformer α) : restrictT F (fullDomain F) = F := by
  funext P x y; simp [restrictT, fullDomain]

/-- ✱43·31. -/
theorem star_43_31 (R : Relation α) :
    restrictT (left R) (fullDomain (left R)) = left R ∧
      restrictT (left R) (fullDomain (left R)) = left R := ⟨restrict_full _, restrict_full _⟩

/-- ✱43·311. -/
theorem star_43_311 (R : Relation α) :
    restrictT (right R) (fullDomain (right R)) = right R ∧
      restrictT (right R) (fullDomain (right R)) = right R := ⟨restrict_full _, restrict_full _⟩

/-- ✱43·312. -/
theorem star_43_312 (R S : Relation α) :
    restrictT (both R S) (fullDomain (both R S)) = both R S ∧
      restrictT (both R S) (fullDomain (both R S)) = both R S := ⟨restrict_full _, restrict_full _⟩

/-- ✱43·34. -/
theorem star_43_34 (R : Relation α) : left R R = right R R ∧ right R R = product R R := ⟨rfl, rfl⟩

private def domain (P : Relation α) : Class α := fun x => ∃ y, P x y
private def range (P : Relation α) : Class α := fun y => ∃ x, P x y
private def image (R : Relation α) (A : Class α) : Class α := fun x => ∃ y, A y ∧ R x y
private def converse (R : Relation α) : Relation α := fun x y => R y x
private def unionImage (F : Relation α → Class α) (L : Class (Relation α)) : Class α :=
  fun x => ∃ P, L P ∧ F P x
private def pointImage (F : Transformer α) (L : Class (Relation α)) : Class (Relation α) :=
  fun P => ∃ Q, L Q ∧ P = F Q

/-- ✱43·4. -/
theorem star_43_4 (R P : Relation α) : image R (domain P) = domain (product R P) := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨z, hP⟩, hR⟩; exact ⟨z, y, hR, hP⟩
  · rintro ⟨z, y, hR, hP⟩; exact ⟨y, ⟨z, hP⟩, hR⟩

/-- ✱43·401. -/
theorem star_43_401 (R P : Relation α) : image (converse R) (range P) = range (product P R) := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨z, hP⟩, hR⟩; exact ⟨z, y, hP, hR⟩
  · rintro ⟨z, y, hP, hR⟩; exact ⟨y, ⟨z, hP⟩, hR⟩

/-- ✱43·41. -/
theorem star_43_41 (R : Relation α) (L : Class (Relation α)) :
    image R (unionImage domain L) = unionImage domain (pointImage (left R) L) := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨P, hL, z, hP⟩, hR⟩; exact ⟨left R P, ⟨P, hL, rfl⟩, z, y, hR, hP⟩
  · rintro ⟨X, ⟨P, hL, rfl⟩, z, y, hR, hP⟩; exact ⟨y, ⟨P, hL, z, hP⟩, hR⟩

/-- ✱43·411. -/
theorem star_43_411 (R : Relation α) (L : Class (Relation α)) :
    image (converse R) (unionImage range L) = unionImage range (pointImage (right R) L) := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨P, hL, z, hP⟩, hR⟩; exact ⟨right R P, ⟨P, hL, rfl⟩, z, y, hP, hR⟩
  · rintro ⟨X, ⟨P, hL, rfl⟩, z, y, hP, hR⟩; exact ⟨y, ⟨P, hL, z, hP⟩, hR⟩

/-- ✱43·42. -/
theorem star_43_42 (R : Relation α) (L : Class (Relation α)) :
    pointImage (left R) L = fun P => ∃ Q, L Q ∧ P = product R Q := rfl
/-- ✱43·421. -/
theorem star_43_421 (R : Relation α) (L : Class (Relation α)) :
    pointImage (right R) L = fun P => ∃ Q, L Q ∧ P = product Q R := rfl
/-- ✱43·43. -/
theorem star_43_43 (R S : Relation α) (L : Class (Relation α)) :
    pointImage (both R S) L = fun P => ∃ Q, L Q ∧ P = product (product R Q) S := rfl

private def subset (A B : Class α) := ∀ x, A x → B x
private def restrictRange (Q : Relation α) (A : Class α) : Relation α := fun x y => Q x y ∧ A y
private def restrictDomain (B : Class α) (R : Relation α) : Relation α := fun x y => B x ∧ R x y

/-- ✱43·48. -/
theorem star_43_48 (P Q : Relation α) (A : Class α) (h : subset (domain P) A) :
    product Q P = product (restrictRange Q A) P := by
  funext x z; apply propext; constructor
  · rintro ⟨y, hQ, hP⟩; exact ⟨y, ⟨hQ, h y ⟨z, hP⟩⟩, hP⟩
  · rintro ⟨y, ⟨hQ, _⟩, hP⟩; exact ⟨y, hQ, hP⟩

/-- ✱43·481. -/
theorem star_43_481 (P R : Relation α) (B : Class α) (h : subset (range P) B) :
    product P R = product P (restrictDomain B R) := by
  funext x z; apply propext; constructor
  · rintro ⟨y, hP, hR⟩; exact ⟨y, hP, h y ⟨x, hP⟩, hR⟩
  · rintro ⟨y, hP, _, hR⟩; exact ⟨y, hP, hR⟩

/-- ✱43·49. -/
theorem star_43_49 (Q : Relation α) (L : Class (Relation α)) (A : Class α)
    (h : ∀ P, L P → subset (domain P) A) :
    pointImage (fun P => product Q P) L = pointImage (fun P => product (restrictRange Q A) P) L := by
  funext X; apply propext; constructor <;> rintro ⟨P, hL, rfl⟩
  · exact ⟨P, hL, star_43_48 P Q A (h P hL)⟩
  · exact ⟨P, hL, (star_43_48 P Q A (h P hL)).symm⟩

/-- ✱43·491. -/
theorem star_43_491 (R : Relation α) (L : Class (Relation α)) (B : Class α)
    (h : ∀ P, L P → subset (range P) B) :
    pointImage (fun P => product P R) L = pointImage (fun P => product P (restrictDomain B R)) L := by
  funext X; apply propext; constructor <;> rintro ⟨P, hL, rfl⟩
  · exact ⟨P, hL, star_43_481 P R B (h P hL)⟩
  · exact ⟨P, hL, (star_43_481 P R B (h P hL)).symm⟩

/-- ✱43·5. -/
theorem star_43_5 (P Q R : Relation α) (A B : Class α)
    (hA : subset (domain P) A) (hB : subset (range P) B) :
    both Q R P = product (product (restrictRange Q A) P) (restrictDomain B R) := by
  unfold both
  rw [star_43_48 P Q A hA]
  apply star_43_481
  intro z
  rintro ⟨x, y, _hQ, hP⟩
  exact hB z ⟨y, hP⟩

/-- ✱43·51. -/
theorem star_43_51 (Q R : Relation α) (L : Class (Relation α)) (A B : Class α)
    (hA : ∀ P, L P → subset (domain P) A) (hB : ∀ P, L P → subset (range P) B) :
    pointImage (both Q R) L =
      pointImage (fun P => product (product (restrictRange Q A) P) (restrictDomain B R)) L := by
  funext X; apply propext; constructor <;> rintro ⟨P, hL, rfl⟩
  · exact ⟨P, hL, star_43_5 P Q R A B (hA P hL) (hB P hL)⟩
  · exact ⟨P, hL, (star_43_5 P Q R A B (hA P hL) (hB P hL)).symm⟩

end PM.Architecture.Star43OpeningKernel3
