import Principia.Architecture.Star36RestrictionKernel

namespace PM.Architecture.Star36RestrictionKernel2

open PM.Architecture.Star36RestrictionKernel

def relUnion (P Q : Relation α) : Relation α := fun x y => P x y ∨ Q x y
def relIncluded (P Q : Relation α) : Prop := ∀ x y, P x y → Q x y
def composition (P Q : Relation α) : Relation α :=
  fun x z => ∃ y, P x y ∧ Q y z
def field (P : Relation α) : Class α := fun x => (∃ y, P x y) ∨ (∃ y, P y x)
def emptyClass : Class α := fun _ => False
def universalClass : Class α := fun _ => True
def emptyRelation : Relation α := fun _ _ => False
def square (a : Class α) : Relation α := fun x y => a x ∧ a y

/-- ✱36·22: composing two relations restricted to the same class is included
in the corresponding restriction of their composition. -/
theorem star_36_22 (P Q : Relation α) (a : Class α) :
    relIncluded (composition (fieldRestrict P a) (fieldRestrict Q a))
      (fieldRestrict (composition P Q) a) := by
  rintro x z ⟨y, ⟨hx, _, hp⟩, ⟨_, hz, hq⟩⟩
  exact ⟨hx, hz, y, hp, hq⟩

/-- ✱36·23: restriction distributes over relation union. -/
theorem star_36_23 (P Q : Relation α) (a : Class α) :
    fieldRestrict (relUnion P Q) a =
      relUnion (fieldRestrict P a) (fieldRestrict Q a) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx, hy, hp | hq⟩
    · exact Or.inl ⟨hx, hy, hp⟩
    · exact Or.inr ⟨hx, hy, hq⟩
  · rintro (⟨hx, hy, hp⟩ | ⟨hx, hy, hq⟩)
    · exact ⟨hx, hy, Or.inl hp⟩
    · exact ⟨hx, hy, Or.inr hq⟩

/-- ✱36·24: enlarging the limiting class enlarges the restricted relation. -/
theorem star_36_24 (P : Relation α) (a b : Class α)
    (hab : ∀ x, a x → b x) :
    relIncluded (fieldRestrict P a) (fieldRestrict P b) := by
  rintro x y ⟨hx, hy, hp⟩
  exact ⟨hab x hx, hab y hy, hp⟩

/-- ✱36·241: relation inclusion is preserved by a common field restriction. -/
theorem star_36_241 (P Q : Relation α) (a : Class α)
    (hpq : relIncluded P Q) :
    relIncluded (fieldRestrict P a) (fieldRestrict Q a) := by
  rintro x y ⟨hx, hy, hp⟩
  exact ⟨hx, hy, hpq x y hp⟩

/-- ✱36·25: a restriction fixes a relation exactly when its field is included
in the limiting class. -/
theorem star_36_25 (P : Relation α) (a : Class α) :
    (∀ x, field P x → a x) ↔ fieldRestrict P a = P := by
  constructor
  · intro h
    funext x y
    apply propext
    exact ⟨fun hp => hp.2.2,
      fun hp => ⟨h x (Or.inl ⟨y, hp⟩), h y (Or.inr ⟨x, hp⟩), hp⟩⟩
  · intro h x hx
    rcases hx with ⟨y, hp⟩ | ⟨y, hp⟩
    · have : fieldRestrict P a x y := by rw [h]; exact hp
      exact this.1
    · have : fieldRestrict P a y x := by rw [h]; exact hp
      exact this.2.1

/-- ✱36·26: if the field of `P` misses `a`, composition with any relation
restricted to `a` is empty in either order. -/
theorem star_36_26 (P Q : Relation α) (a : Class α)
    (hdisjoint : ∀ x, field P x → a x → False) :
    composition P (fieldRestrict Q a) = emptyRelation ∧
      composition (fieldRestrict Q a) P = emptyRelation := by
  constructor
  · funext x z
    apply propext
    constructor
    · rintro ⟨y, hp, hy, _, _⟩
      exact False.elim (hdisjoint y (Or.inr ⟨x, hp⟩) hy)
    · exact False.elim
  · funext x z
    apply propext
    constructor
    · rintro ⟨y, ⟨_, hy, _⟩, hp⟩
      exact False.elim (hdisjoint y (Or.inl ⟨z, hp⟩) hy)
    · exact False.elim

/-- ✱36·27: restriction to the null class is the null relation. -/
theorem star_36_27 (P : Relation α) :
    fieldRestrict P emptyClass = emptyRelation := by
  funext x y
  apply propext
  exact ⟨fun h => h.1, False.elim⟩

/-- ✱36·28: restriction to the universal class changes nothing. -/
theorem star_36_28 (P : Relation α) :
    fieldRestrict P universalClass = P := by
  funext x y
  apply propext
  exact ⟨fun h => h.2.2, fun hp => ⟨True.intro, True.intro, hp⟩⟩

/-- ✱36·29: field restriction is intersection with the square of its class. -/
theorem star_36_29 (P : Relation α) (a : Class α) :
    fieldRestrict P a = relInter P (square a) := by
  funext x y
  apply propext
  exact ⟨fun ⟨hx, hy, hp⟩ => ⟨hp, hx, hy⟩,
    fun ⟨hp, hx, hy⟩ => ⟨hx, hy, hp⟩⟩

/-- ✱36·3: only the part of the limiting class lying in the relation's field
affects its restriction. -/
theorem star_36_3 (P : Relation α) (a : Class α) :
    fieldRestrict P a = fieldRestrict P (classInter a (field P)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx, hy, hp⟩
    exact ⟨⟨hx, Or.inl ⟨y, hp⟩⟩, ⟨hy, Or.inr ⟨x, hp⟩⟩, hp⟩
  · rintro ⟨⟨hx, _⟩, ⟨hy, _⟩, hp⟩
    exact ⟨hx, hy, hp⟩

end PM.Architecture.Star36RestrictionKernel2
