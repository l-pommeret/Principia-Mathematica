import Principia.Architecture.Star25MiddleKernel

/-! Ten consecutive PM I propositions ✱25·311–✱25·38 (p. 243). -/

namespace PM.Architecture.Star25LaterKernel

open PM.Architecture.Star25OpeningKernel
open PM.Architecture.Star25MiddleKernel

/-- PM I ✱25·311. -/
theorem star_25_311 (relation other : Relation Left Right) :
    Included relation (complement other) ↔
      intersection relation other = nullRelation Left Right := by
  constructor
  · intro included
    funext x y
    apply propext
    exact ⟨fun h => (included x y h.1) h.2, fun impossible => False.elim impossible⟩
  · intro empty x y member otherMember
    have : nullRelation Left Right x y := by
      rw [← empty]
      exact ⟨member, otherMember⟩
    exact this

/-- PM I ✱25·312. -/
theorem star_25_312 (relation other : Relation Left Right) :
    Included (complement relation) other ↔
      union relation other = universalRelation Left Right := by
  constructor
  · intro included
    funext x y
    apply propext
    constructor
    · intro _
      exact True.intro
    · intro _
      by_cases member : relation x y
      · exact Or.inl member
      · exact Or.inr (included x y member)
  · intro total x y absent
    have : union relation other x y := by
      rw [total]
      exact True.intro
    cases this with
    | inl member => exact False.elim (absent member)
    | inr member => exact member

/-- PM I ✱25·313. -/
theorem star_25_313 (relation other : Relation Left Right) :
    intersection relation other = nullRelation Left Right ↔
      difference relation other = relation := by
  constructor
  · intro disjoint
    funext x y
    apply propext
    constructor
    · exact fun h => h.1
    · intro member
      refine ⟨member, ?_⟩
      intro otherMember
      have : nullRelation Left Right x y := by
        rw [← disjoint]
        exact ⟨member, otherMember⟩
      exact this
  · intro retained
    funext x y
    apply propext
    constructor
    · rintro ⟨member, otherMember⟩
      have differenceMember : difference relation other x y := by
        rw [retained]
        exact member
      exact differenceMember.2 otherMember
    · intro impossible
      exact False.elim impossible

/-- PM I ✱25·32. -/
theorem star_25_32 (relation other : Relation Left Right) :
    union relation other = nullRelation Left Right ↔
      relation = nullRelation Left Right ∧
        other = nullRelation Left Right := by
  constructor
  · intro empty
    constructor
    · funext x y
      apply propext
      exact ⟨fun h => by rw [← empty]; exact Or.inl h,
        fun impossible => False.elim impossible⟩
    · funext x y
      apply propext
      exact ⟨fun h => by rw [← empty]; exact Or.inr h,
        fun impossible => False.elim impossible⟩
  · rintro ⟨rfl, rfl⟩
    funext x y
    apply propext
    exact ⟨fun h => h.elim id id, fun impossible => False.elim impossible⟩

/-- PM I ✱25·33. -/
theorem star_25_33 (relation other : Relation Left Right) :
    relation = universalRelation Left Right →
      union relation other = universalRelation Left Right := by
  rintro rfl
  funext x y
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Or.inl True.intro⟩

/-- PM I ✱25·34. -/
theorem star_25_34 (relation other : Relation Left Right) :
    relation = nullRelation Left Right →
      intersection relation other = nullRelation Left Right := by
  rintro rfl
  funext x y
  apply propext
  exact ⟨fun h => h.1, fun impossible => False.elim impossible⟩

/-- PM I ✱25·35. -/
theorem star_25_35 (relation other : Relation Left Right) :
    relation = universalRelation Left Right →
      intersection relation other = other := by
  rintro rfl
  funext x y
  apply propext
  exact ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩

/-- PM I ✱25·36. -/
theorem star_25_36 (relation other : Relation Left Right) :
    relation = nullRelation Left Right → union relation other = other := by
  rintro rfl
  funext x y
  apply propext
  constructor
  · rintro (impossible | h)
    · exact False.elim impossible
    · exact h
  · exact Or.inr

/-- PM I ✱25·37: disjointness iff any related pairs differ in at least one
coordinate. -/
theorem star_25_37 (relation other : Relation Left Right) :
    intersection relation other = nullRelation Left Right ↔
      ∀ x y z w, relation x y → other z w → x ≠ z ∨ y ≠ w := by
  constructor
  · intro disjoint x y z w hxy hzw
    by_cases hxz : x = z
    · right
      intro hyw
      subst z
      subst w
      have : nullRelation Left Right x y := by
        rw [← disjoint]
        exact ⟨hxy, hzw⟩
      exact this
    · exact Or.inl hxz
  · intro separated
    funext x y
    apply propext
    constructor
    · rintro ⟨hr, hs⟩
      cases separated x y x y hr hs with
      | inl h => exact h rfl
      | inr h => exact h rfl
    · intro impossible
      exact False.elim impossible

/-- PM I ✱25·38. -/
theorem star_25_38 (relation other : Relation Left Right) :
    intersection relation other = nullRelation Left Right →
      relation ≠ other ∨
        relation = nullRelation Left Right ∧
          other = nullRelation Left Right := by
  intro disjoint
  by_cases equal : relation = other
  · right
    subst other
    have emptyRelation : relation = nullRelation Left Right := by
      funext x y
      apply propext
      constructor
      · intro member
        have : nullRelation Left Right x y := by
          rw [← disjoint]
          exact ⟨member, member⟩
        exact this
      · intro impossible
        exact False.elim impossible
    exact ⟨emptyRelation, emptyRelation⟩
  · exact Or.inl equal

end PM.Architecture.Star25LaterKernel
