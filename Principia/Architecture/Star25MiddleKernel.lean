import Principia.Architecture.Star25OpeningKernel

/-! Ten consecutive PM I propositions ✱25·15–✱25·31 (pp. 242–243). -/

namespace PM.Architecture.Star25MiddleKernel

open PM.Architecture.Star25OpeningKernel

def intersection (relation other : Relation Left Right) : Relation Left Right :=
  fun x y => relation x y ∧ other x y

def union (relation other : Relation Left Right) : Relation Left Right :=
  fun x y => relation x y ∨ other x y

def difference (relation other : Relation Left Right) : Relation Left Right :=
  intersection relation (complement other)

/-- PM I ✱25·15. -/
theorem star_25_15 (relation : Relation Left Right) :
    (∀ x y, ¬ relation x y) ↔ relation = nullRelation Left Right :=
  star_25_103 relation

/-- PM I ✱25·17. -/
theorem star_25_17 (relation : Relation Left Right) :
    relation = universalRelation Left Right ↔
      complement relation = nullRelation Left Right := by
  constructor
  · rintro rfl
    funext x y
    apply propext
    exact ⟨fun h => h True.intro, fun impossible => False.elim impossible⟩
  · intro emptyComplement
    funext x y
    apply propext
    constructor
    · intro _
      exact True.intro
    · intro _
      apply Classical.byContradiction
      intro absent
      have : nullRelation Left Right x y := by
        rw [← emptyComplement]
        exact absent
      exact this

/-- PM I ✱25·21. -/
theorem star_25_21 (relation : Relation Left Right) :
    intersection relation (complement relation) = nullRelation Left Right := by
  funext x y
  apply propext
  exact ⟨fun ⟨h, hn⟩ => hn h, fun impossible => False.elim impossible⟩

/-- PM I ✱25·22. -/
theorem star_25_22 (relation : Relation Left Right) :
    union relation (complement relation) = universalRelation Left Right := by
  funext x y
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Classical.em (relation x y)⟩

/-- PM I ✱25·23. -/
theorem star_25_23 (relation : Relation Left Right) :
    intersection relation (nullRelation Left Right) =
      nullRelation Left Right := by
  funext x y
  apply propext
  exact ⟨fun h => h.2, fun impossible => False.elim impossible⟩

/-- PM I ✱25·24. -/
theorem star_25_24 (relation : Relation Left Right) :
    union relation (nullRelation Left Right) = relation := by
  funext x y
  apply propext
  constructor
  · rintro (h | impossible)
    · exact h
    · exact False.elim impossible
  · exact Or.inl

/-- PM I ✱25·26. -/
theorem star_25_26 (relation : Relation Left Right) :
    intersection relation (universalRelation Left Right) = relation := by
  funext x y
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩

/-- PM I ✱25·27. -/
theorem star_25_27 (relation : Relation Left Right) :
    union relation (universalRelation Left Right) =
      universalRelation Left Right := by
  funext x y
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Or.inr True.intro⟩

/-- PM I ✱25·3. -/
theorem star_25_3 (relation other : Relation Left Right) :
    Included relation other ↔
      difference relation other = nullRelation Left Right := by
  constructor
  · intro included
    funext x y
    apply propext
    exact ⟨fun h => h.2 (included x y h.1), fun impossible => False.elim impossible⟩
  · intro emptyDifference x y member
    apply Classical.byContradiction
    intro absent
    have : nullRelation Left Right x y := by
      rw [← emptyDifference]
      exact ⟨member, absent⟩
    exact this

/-- PM I ✱25·31. -/
theorem star_25_31 (relation other : Relation Left Right) :
    Included relation other ↔
      union (complement relation) other = universalRelation Left Right := by
  constructor
  · intro included
    funext x y
    apply propext
    constructor
    · intro _
      exact True.intro
    · intro _
      by_cases member : relation x y
      · exact Or.inr (included x y member)
      · exact Or.inl member
  · intro total x y member
    have all : union (complement relation) other x y := by
      rw [total]
      exact True.intro
    cases all with
    | inl absent => exact False.elim (absent member)
    | inr present => exact present

end PM.Architecture.Star25MiddleKernel
