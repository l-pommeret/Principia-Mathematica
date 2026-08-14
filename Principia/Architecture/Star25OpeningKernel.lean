/-!
# PM I ✱25·1–✱25·141

Eleven consecutive propositions from the opening of ✱25 (first edition,
pp. 241–242).  A relation retains both assigned argument types.
-/

namespace PM.Architecture.Star25OpeningKernel

abbrev Relation (Left : Sort u) (Right : Sort v) := Left → Right → Prop

def Included (relation other : Relation Left Right) : Prop :=
  ∀ x y, relation x y → other x y

def universalRelation (Left : Sort u) (Right : Sort v) : Relation Left Right :=
  fun _ _ => True

def nullRelation (Left : Sort u) (Right : Sort v) : Relation Left Right :=
  fun _ _ => False

def complement (relation : Relation Left Right) : Relation Left Right :=
  fun x y => ¬ relation x y

def existsRelation (relation : Relation Left Right) : Prop :=
  ∃ x y, relation x y

/-- ✱25·01. `V̇ = x̂ŷ(x = x . y = y) Df`. -/
def star_25_01 : Relation Left Right := fun x y => x = x ∧ y = y

/-- ✱25·02. `Λ̇ = −̇V̇ Df`. -/
def star_25_02 : Relation Left Right := complement (universalRelation Left Right)

/-- ✱25·03. `∃̇!R .=. (∃x,y) . xRy Df`. -/
def star_25_03 (relation : Relation Left Right) : Prop := ∃ x y, relation x y

/-- PM I ✱25·1: the null relation differs from the universal relation. -/
theorem star_25_1 [Nonempty Left] [Nonempty Right] :
    nullRelation Left Right ≠ universalRelation Left Right := by
  intro equality
  let x : Left := Classical.choice inferInstance
  let y : Right := Classical.choice inferInstance
  have : nullRelation Left Right x y := by
    rw [equality]
    exact True.intro
  exact this

/-- PM I ✱25·101: the universal relation is the complement of null. -/
theorem star_25_101 :
    universalRelation Left Right = complement (nullRelation Left Right) := by
  funext x y
  apply propext
  exact ⟨fun _ impossible => impossible, fun _ => True.intro⟩

/-- PM I ✱25·102. -/
theorem star_25_102 (phi : Relation Left Right) :
    (∀ x y, phi x y) ↔ phi = universalRelation Left Right := by
  constructor
  · intro holds
    funext x y
    apply propext
    exact ⟨fun _ => True.intro, fun _ => holds x y⟩
  · rintro rfl x y
    exact True.intro

/-- PM I ✱25·103. -/
theorem star_25_103 (phi : Relation Left Right) :
    (∀ x y, ¬ phi x y) ↔ phi = nullRelation Left Right := by
  constructor
  · intro never
    funext x y
    apply propext
    exact ⟨fun h => False.elim (never x y h), fun impossible => False.elim impossible⟩
  · rintro rfl x y impossible
    exact impossible

/-- PM I ✱25·104. -/
theorem star_25_104 (x : Left) (y : Right) :
    universalRelation Left Right x y := True.intro

/-- PM I ✱25·105. -/
theorem star_25_105 (x : Left) (y : Right) :
    ¬ nullRelation Left Right x y := by
  intro impossible
  exact impossible

/-- PM I ✱25·11: every relation is included in the universal relation. -/
theorem star_25_11 (relation : Relation Left Right) :
    Included relation (universalRelation Left Right) := by
  intro x y member
  exact True.intro

/-- PM I ✱25·12: the null relation is included in every relation. -/
theorem star_25_12 (relation : Relation Left Right) :
    Included (nullRelation Left Right) relation := by
  intro x y impossible
  exact False.elim impossible

/-- PM I ✱25·13. -/
theorem star_25_13 (relation : Relation Left Right) :
    relation = nullRelation Left Right ↔
      Included relation (nullRelation Left Right) := by
  constructor
  · rintro rfl
    exact star_25_12 _
  · intro inclusion
    funext x y
    apply propext
    exact ⟨inclusion x y, fun impossible => False.elim impossible⟩

/-- PM I ✱25·14. -/
theorem star_25_14 (relation : Relation Left Right) :
    (∀ x y, relation x y) ↔ relation = universalRelation Left Right :=
  star_25_102 relation

/-- PM I ✱25·141. -/
theorem star_25_141 (relation : Relation Left Right) :
    Included (universalRelation Left Right) relation ↔
      universalRelation Left Right = relation := by
  constructor
  · intro inclusion
    funext x y
    apply propext
    exact ⟨fun _ => inclusion x y True.intro, fun _ => True.intro⟩
  · rintro rfl
    exact star_25_11 _

end PM.Architecture.Star25OpeningKernel
