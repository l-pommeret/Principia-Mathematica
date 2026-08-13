/-! PM I ✱41·17–23: the next ten consecutive relation-class laws. -/

namespace PM.Architecture.Star41MiddleKernel

abbrev Relation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) := Relation α β → Prop

def subrel (R S : Relation α β) : Prop := ∀ x y, R x y → S x y
def product (collection : RelationClass α β) : Relation α β :=
  fun x y => ∀ R, collection R → R x y
def sum (collection : RelationClass α β) : Relation α β :=
  fun x y => ∃ R, collection R ∧ R x y
def relInter (R S : Relation α β) : Relation α β :=
  fun x y => R x y ∧ S x y
def relUnion (R S : Relation α β) : Relation α β :=
  fun x y => R x y ∨ S x y
def classInter (collection larger : RelationClass α β) : RelationClass α β :=
  fun R => collection R ∧ larger R
def classUnion (collection larger : RelationClass α β) : RelationClass α β :=
  fun R => collection R ∨ larger R
def emptyRelation : Relation α β := fun _ _ => False
def universalRelation : Relation α β := fun _ _ => True
def emptyClass : RelationClass α β := fun _ => False

/-- ✱41·17. -/
theorem star_41_17 (collection larger : RelationClass α β) :
    subrel (relUnion (product collection) (product larger))
      (product (classInter collection larger)) := by
  intro x y h R hR
  exact h.elim (fun hp => hp R hR.1) (fun hp => hp R hR.2)

/-- ✱41·171. -/
theorem star_41_171 (collection larger : RelationClass α β) :
    relUnion (sum collection) (sum larger) =
      sum (classUnion collection larger) := by
  funext x y
  apply propext
  constructor
  · intro h
    exact h.elim
      (fun ⟨R, hR, hxy⟩ => ⟨R, Or.inl hR, hxy⟩)
      (fun ⟨R, hR, hxy⟩ => ⟨R, Or.inr hR, hxy⟩)
  · rintro ⟨R, hR, hxy⟩
    exact hR.elim
      (fun hc => Or.inl ⟨R, hc, hxy⟩)
      (fun hl => Or.inr ⟨R, hl, hxy⟩)

/-- ✱41·18. -/
theorem star_41_18 (collection larger : RelationClass α β) :
    product (classUnion collection larger) =
      relInter (product collection) (product larger) := by
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨fun R hR => h R (Or.inl hR), fun R hR => h R (Or.inr hR)⟩
  · rintro ⟨hc, hl⟩ R hR
    exact hR.elim (hc R) (hl R)

/-- ✱41·181. -/
theorem star_41_181 (collection larger : RelationClass α β) :
    subrel (sum (classInter collection larger))
      (relInter (sum collection) (sum larger)) := by
  rintro x y ⟨R, ⟨hc, hl⟩, hxy⟩
  exact ⟨⟨R, hc, hxy⟩, ⟨R, hl, hxy⟩⟩

/-- ✱41·19. Membership in a relational sum is characterized by all its
upper bounds. -/
theorem star_41_19 (collection : RelationClass α β) (x : α) (y : β) :
    sum collection x y ↔
      ∀ S, (∀ R, collection R → subrel R S) → S x y := by
  constructor
  · rintro ⟨R, hR, hxy⟩ S hS
    exact hS R hR x y hxy
  · intro h
    exact h (sum collection) (fun R hR u v huv => ⟨R, hR, huv⟩)

/-- ✱41·2. The product of the empty relation class is universal. -/
theorem star_41_2 :
    product (emptyClass : RelationClass α β) = universalRelation := by
  funext x y
  apply propext
  exact ⟨fun _ => True.intro, fun _ R hR => False.elim hR⟩

/-- ✱41·21. The sum of the empty relation class is empty. -/
theorem star_41_21 :
    sum (emptyClass : RelationClass α β) = emptyRelation := by
  funext x y
  apply propext
  exact ⟨fun ⟨_, hR, _⟩ => False.elim hR, False.elim⟩

/-- ✱41·22. A product containing the empty relation is empty. -/
theorem star_41_22 (collection : RelationClass α β) :
    collection emptyRelation → product collection = emptyRelation := by
  intro hempty
  funext x y
  apply propext
  exact ⟨fun h => h emptyRelation hempty, False.elim⟩

/-- ✱41·221. A sum containing the universal relation is universal. -/
theorem star_41_221 (collection : RelationClass α β) :
    collection universalRelation → sum collection = universalRelation := by
  intro huniv
  funext x y
  apply propext
  exact ⟨fun _ => True.intro, fun _ => ⟨universalRelation, huniv, True.intro⟩⟩

/-- ✱41·23. For a nonempty class of relations, its product is contained in
its sum. -/
theorem star_41_23 (collection : RelationClass α β) :
    (∃ R, collection R) → subrel (product collection) (sum collection) := by
  rintro ⟨R, hR⟩ x y hprod
  exact ⟨R, hR, hprod R hR⟩

end PM.Architecture.Star41MiddleKernel
