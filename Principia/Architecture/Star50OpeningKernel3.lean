namespace PM.Architecture.Star50OpeningKernel3

universe u

abbrev Relation (α : Sort u) := α → α → Prop
abbrev ClassExtension (α : Sort u) := α → Prop

def I : Relation α := fun x y => x = y
def J : Relation α := fun x y => x ≠ y
def converse (R : Relation α) : Relation α := fun x y => R y x
def comp (R S : Relation α) : Relation α := fun x z => ∃ y, R x y ∧ S y z
def inter (R S : Relation α) : Relation α := fun x y => R x y ∧ S x y
def empty : Relation α := fun _ _ => False
def Included (R S : Relation α) : Prop := ∀ x y, R x y → S x y
def NonemptyRelation (R : Relation α) : Prop := ∃ x y, R x y
def leftRestrict (A : ClassExtension α) (R : Relation α) : Relation α :=
  fun x y => A x ∧ R x y
def rightRestrict (R : Relation α) (A : ClassExtension α) : Relation α :=
  fun x y => R x y ∧ A y

private theorem relationExt {R S : Relation α} (h : ∀ x y, R x y ↔ S x y) :
    R = S := by
  funext x y
  exact propext (h x y)

private theorem emptyOfNoWitness (R : Relation α)
    (h : ∀ x y, ¬ R x y) : R = empty := by
  apply relationExt
  intro x y
  exact ⟨fun hR => False.elim (h x y hR), False.elim⟩

/-- PM I ✱50·35: diversity is inhabited on relations. -/
theorem star_50_35 [Nonempty α] : ∃ R S : Relation α, R ≠ S := by
  let ⟨x⟩ := (inferInstance : Nonempty α)
  refine ⟨empty, fun _ _ => True, ?_⟩
  intro h
  exact Eq.mpr (congrFun (congrFun h x) x) trivial

/-- PM I ✱50·4. -/
theorem star_50_4 (R : Relation α) :
    comp R I = R ∧ comp I R = R := by
  constructor <;> apply relationExt <;> intro x z <;> constructor
  · rintro ⟨y, hxy, hyz⟩
    cases hyz
    exact hxy
  · intro hxz
    exact ⟨z, hxz, rfl⟩
  · rintro ⟨y, hxy, hyz⟩
    cases hxy
    exact hyz
  · intro hxz
    exact ⟨x, rfl, hxz⟩

private theorem firstAsymmetry (R P : Relation α) :
    Included (comp R (converse P)) J ↔ inter R P = empty := by
  constructor
  · intro h
    apply emptyOfNoWitness
    intro x y hBoth
    exact h x x ⟨y, hBoth.1, hBoth.2⟩ rfl
  · intro h x z
    rintro ⟨y, hR, hP⟩ hxz
    subst z
    have point := congrFun (congrFun h x) y
    exact Eq.mp point ⟨hR, hP⟩

private theorem secondAsymmetry (R P : Relation α) :
    Included (comp (converse R) P) J ↔ inter R P = empty := by
  constructor
  · intro h
    apply emptyOfNoWitness
    intro x y hBoth
    exact h y y ⟨x, hBoth.1, hBoth.2⟩ rfl
  · intro h x z
    rintro ⟨y, hR, hP⟩ hxz
    subst z
    have point := congrFun (congrFun h y) x
    exact Eq.mp point ⟨hR, hP⟩

/-- PM I ✱50·41, retaining all three equivalent members. -/
theorem star_50_41 (R P : Relation α) :
    (Included (comp R (converse P)) J ↔ Included (comp (converse R) P) J) ∧
    (Included (comp (converse R) P) J ↔ inter R P = empty) :=
  ⟨(firstAsymmetry R P).trans (secondAsymmetry R P).symm,
    secondAsymmetry R P⟩

/-- PM I ✱50·42. -/
theorem star_50_42 : comp (I : Relation α) I = I := (star_50_4 I).1

/-- PM I ✱50·43. -/
theorem star_50_43 (R : Relation α) :
    Included (comp R R) J ↔ inter R (converse R) = empty :=
  firstAsymmetry R (converse R)

/-- PM I ✱50·44. -/
theorem star_50_44 (R : Relation α) :
    NonemptyRelation (inter R I) → NonemptyRelation (inter (comp R R) I) := by
  rintro ⟨x, y, hR, hEq⟩
  subst y
  exact ⟨x, x, ⟨x, hR, hR⟩, rfl⟩

/-- PM I ✱50·45. -/
theorem star_50_45 (R : Relation α) :
    Included (comp R R) J → Included R J := by
  intro h x y hR hEq
  subst y
  exact h x x ⟨x, hR, hR⟩ rfl

/-- PM I ✱50·46. -/
theorem star_50_46 (R : Relation α) :
    inter R (converse R) = empty → Included R J := by
  intro h
  exact star_50_45 R ((star_50_43 R).mpr h)

/-- PM I ✱50·47, under the printed transitivity hypothesis. -/
theorem star_50_47 (R : Relation α) (hTrans : Included (comp R R) R) :
    (Included R J ↔ Included (comp R R) J) ∧
    (Included (comp R R) J ↔ inter R (converse R) = empty) := by
  constructor
  · constructor
    · intro h x y hR2
      exact h x y (hTrans x y hR2)
    · exact star_50_45 R
  · exact star_50_43 R

/-- PM I ✱50·5. -/
theorem star_50_5 (A : ClassExtension α) :
    leftRestrict A I = rightRestrict I A ∧
    rightRestrict I A = leftRestrict A (rightRestrict I A) := by
  constructor <;> apply relationExt <;> intro x y <;> constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨hy, rfl, hy⟩
  · rintro ⟨hx, rfl, hy⟩
    exact ⟨rfl, hy⟩

end PM.Architecture.Star50OpeningKernel3
