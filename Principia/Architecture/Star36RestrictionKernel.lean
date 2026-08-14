namespace PM.Architecture.Star36RestrictionKernel

/-! PM I ✱36·01–✱36·21: relations with the same class restriction on both fields. -/

abbrev Class (α : Type u) := α → Prop
abbrev Relation (α : Type u) := α → α → Prop

def classInter (a b : Class α) : Class α := fun x => a x ∧ b x
def relInter (P Q : Relation α) : Relation α := fun x y => P x y ∧ Q x y
def leftRestrict (a : Class α) (P : Relation α) : Relation α :=
  fun x y => a x ∧ P x y
def rightRestrict (P : Relation α) (a : Class α) : Relation α :=
  fun x y => P x y ∧ a y

/-- PM's `P ⥏ α`: restrict both the domain and converse domain to `α`. -/
def fieldRestrict (P : Relation α) (a : Class α) : Relation α :=
  fun x y => a x ∧ a y ∧ P x y

/-- ✱36·01. `P⟏α = α◁P▷α Df`. -/
def star_36_01 (P : Relation α) (a : Class α) : Relation α :=
  rightRestrict (leftRestrict a P) a

/-- ✱36·11, the asserted form of the definition. -/
theorem star_36_11 (P : Relation α) (a : Class α) :
    fieldRestrict P a = rightRestrict (leftRestrict a P) a := by
  funext x y
  apply propext
  exact ⟨fun ⟨hx, hy, hp⟩ => ⟨⟨hx, hp⟩, hy⟩,
    fun ⟨⟨hx, hp⟩, hy⟩ => ⟨hx, hy, hp⟩⟩

/-- ✱36·13, membership in the restricted relation. -/
theorem star_36_13 (P : Relation α) (a : Class α) (x y : α) :
    fieldRestrict P a x y ↔ a x ∧ a y ∧ P x y := by
  rfl

/-- ✱36·2, intersection of two independently restricted relations. -/
theorem star_36_2 (P Q : Relation α) (a b : Class α) :
    relInter (fieldRestrict P a) (fieldRestrict Q b) =
      fieldRestrict (relInter P Q) (classInter a b) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hax, hay, hp⟩, ⟨hbx, hby, hq⟩⟩
    exact ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp, hq⟩
  · rintro ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp, hq⟩
    exact ⟨⟨hax, hay, hp⟩, ⟨hbx, hby, hq⟩⟩

/-- ✱36·201, the equal-relation instance of ✱36·2. -/
theorem star_36_201 (P : Relation α) (a b : Class α) :
    relInter (fieldRestrict P a) (fieldRestrict P b) =
      fieldRestrict P (classInter a b) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hax, hay, hp⟩, ⟨hbx, hby, _⟩⟩
    exact ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp⟩
  · rintro ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp⟩
    exact ⟨⟨hax, hay, hp⟩, ⟨hbx, hby, hp⟩⟩

/-- ✱36·202, the equal-class instance of ✱36·2. -/
theorem star_36_202 (P Q : Relation α) (a : Class α) :
    relInter (fieldRestrict P a) (fieldRestrict Q a) =
      fieldRestrict (relInter P Q) a := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hx, hy, hp⟩, ⟨_, _, hq⟩⟩
    exact ⟨hx, hy, hp, hq⟩
  · rintro ⟨hx, hy, hp, hq⟩
    exact ⟨⟨hx, hy, hp⟩, ⟨hx, hy, hq⟩⟩

/-- ✱36·203, intersection with an unrestricted relation. -/
theorem star_36_203 (P Q : Relation α) (a : Class α) :
    relInter (fieldRestrict P a) Q =
      fieldRestrict (relInter P Q) a := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hx, hy, hp⟩, hq⟩
    exact ⟨hx, hy, hp, hq⟩
  · rintro ⟨hx, hy, hp, hq⟩
    exact ⟨⟨hx, hy, hp⟩, hq⟩

/-- ✱36·21, iterated field restriction. -/
theorem star_36_21 (P : Relation α) (a b : Class α) :
    fieldRestrict (fieldRestrict P a) b =
      fieldRestrict P (classInter a b) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hbx, hby, hax, hay, hp⟩
    exact ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp⟩
  · rintro ⟨⟨hax, hbx⟩, ⟨hay, hby⟩, hp⟩
    exact ⟨hbx, hby, hax, hay, hp⟩

end PM.Architecture.Star36RestrictionKernel
