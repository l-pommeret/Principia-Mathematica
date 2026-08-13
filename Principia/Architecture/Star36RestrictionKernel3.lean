import Principia.Architecture.Star36RestrictionKernel2

namespace PM.Architecture.Star36RestrictionKernel3

open PM.Architecture.Star36RestrictionKernel
open PM.Architecture.Star36RestrictionKernel2

def converse (P : Relation α) : Relation α := fun x y => P y x
def domain (P : Relation α) : Class α := fun x => ∃ y, P x y
def converseDomain (P : Relation α) : Class α := fun y => ∃ x, P x y

/-- ✱36·31: when the limiting class misses the field, the restriction is
the null relation. -/
theorem star_36_31 (P : Relation α) (a : Class α)
    (h : classInter a (field P) = Star36RestrictionKernel2.emptyClass) :
    fieldRestrict P a = Star36RestrictionKernel2.emptyRelation := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx, _, hp⟩
    have hempty : Star36RestrictionKernel2.emptyClass x := by
      rw [← h]
      exact ⟨hx, Or.inl ⟨y, hp⟩⟩
    exact hempty
  · exact False.elim

/-- ✱36·32: two limiting classes with the same intersection with the field
give the same restricted relation. -/
theorem star_36_32 (P : Relation α) (a b : Class α)
    (h : classInter a (field P) = classInter b (field P)) :
    fieldRestrict P a = fieldRestrict P b := by
  rw [star_36_3 P a, star_36_3 P b, h]

/-- ✱36·33: restriction to the relation's field changes nothing. -/
theorem star_36_33 (P : Relation α) : fieldRestrict P (field P) = P := by
  exact (star_36_25 P (field P)).mp (fun _ hp => hp)

/-- ✱36·34: converse commutes with a common field restriction. -/
theorem star_36_34 (P : Relation α) (a : Class α) :
    converse (fieldRestrict P a) = fieldRestrict (converse P) a := by
  funext x y
  apply propext
  exact ⟨fun ⟨hy, hx, hp⟩ => ⟨hx, hy, hp⟩,
    fun ⟨hx, hy, hp⟩ => ⟨hy, hx, hp⟩⟩

/-- ✱36·35: the square of a restricted relation is included in the
restriction of its square. -/
theorem star_36_35 (P : Relation α) (a : Class α) :
    relIncluded (composition (fieldRestrict P a) (fieldRestrict P a))
      (fieldRestrict (composition P P) a) := by
  exact star_36_22 P P a

/-- ✱36·4: if the limiting class misses either the domain or converse domain
of `R`, adjoining `R` does not affect the restricted relation. -/
theorem star_36_4 (R S : Relation α) (a : Class α)
    (h : classInter a (domain R) = Star36RestrictionKernel2.emptyClass ∨
      classInter a (converseDomain R) = Star36RestrictionKernel2.emptyClass) :
    fieldRestrict (relUnion R S) a = fieldRestrict S a := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx, hy, hr | hs⟩
    · cases h with
      | inl hd =>
          have hempty : Star36RestrictionKernel2.emptyClass x := by
            rw [← hd]
            exact ⟨hx, ⟨y, hr⟩⟩
          exact False.elim hempty
      | inr hc =>
          have hempty : Star36RestrictionKernel2.emptyClass y := by
            rw [← hc]
            exact ⟨hy, ⟨x, hr⟩⟩
          exact False.elim hempty
    · exact ⟨hx, hy, hs⟩
  · rintro ⟨hx, hy, hs⟩
    exact ⟨hx, hy, Or.inr hs⟩

end PM.Architecture.Star36RestrictionKernel3
