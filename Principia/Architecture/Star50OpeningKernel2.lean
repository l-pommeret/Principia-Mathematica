namespace PM.Architecture.Star50OpeningKernel2

universe u

abbrev Relation (α : Sort u) := α → α → Prop
abbrev ClassExtension (α : Sort u) := α → Prop

def I : Relation α := fun x y => x = y
def J : Relation α := fun x y => x ≠ y
def converse (R : Relation α) : Relation α := fun x y => R y x
def Included (R S : Relation α) : Prop := ∀ x y, R x y → S x y
def domain (R : Relation α) : ClassExtension α := fun x => ∃ y, R x y
def converseDomain (R : Relation α) : ClassExtension α := fun y => ∃ x, R x y
def field (R : Relation α) : ClassExtension α :=
  fun x => domain R x ∨ converseDomain R x
def universal : ClassExtension α := fun _ => True

private theorem relationExt {R S : Relation α} (h : ∀ x y, R x y ↔ S x y) :
    R = S := by
  funext x y
  exact propext (h x y)

private theorem classExt {A B : ClassExtension α} (h : ∀ x, A x ↔ B x) :
    A = B := by
  funext x
  exact propext (h x)

/-- PM I ✱50·2. -/
theorem star_50_2 : (I : Relation α) = converse I := by
  apply relationExt
  intro x y
  exact eq_comm

/-- PM I ✱50·21. -/
theorem star_50_21 : (J : Relation α) = converse J := by
  apply relationExt
  intro x y
  exact ne_comm

/-- PM I ✱50·22. -/
theorem star_50_22 (R : Relation α) :
    Included R I ↔ Included (converse R) I := by
  constructor <;> intro h x y hR
  · exact (h y x hR).symm
  · exact (h y x hR).symm

/-- PM I ✱50·23. -/
theorem star_50_23 (R : Relation α) :
    Included R J ↔ Included (converse R) J := by
  constructor <;> intro h x y hR
  · exact (h y x hR).symm
  · exact (h y x hR).symm

/-- PM I ✱50·24. -/
theorem star_50_24 (R : Relation α) :
    Included R J ↔ ∀ x, ¬ R x x := by
  constructor
  · intro h x hx
    exact h x x hx rfl
  · intro h x y hxy hEq
    subst y
    exact h x hxy

/-- PM I ✱50·3. -/
theorem star_50_3 : ∀ x : α, I x x := fun _ => rfl

/-- PM I ✱50·31. -/
theorem star_50_31 :
    (domain (I : Relation α) = universal) ∧
      converseDomain (I : Relation α) = universal := by
  constructor <;> apply classExt <;> intro x <;> constructor
  · exact fun _ => trivial
  · exact fun _ => ⟨x, rfl⟩
  · exact fun _ => trivial
  · exact fun _ => ⟨x, rfl⟩

/-- PM I ✱50·32. -/
theorem star_50_32 : field (I : Relation α) = universal := by
  apply classExt
  intro x
  constructor
  · exact fun _ => trivial
  · exact fun _ => Or.inl ⟨x, rfl⟩

/-- PM I ✱50·33. -/
theorem star_50_33 (hJ : ∃ a b : α, J a b) :
    domain (J : Relation α) = universal ∧
    converseDomain (J : Relation α) = universal ∧
    field (J : Relation α) = universal := by
  obtain ⟨a, b, hab⟩ := hJ
  have everyHasDifferent : ∀ x : α, ∃ y, x ≠ y := by
    intro x
    by_cases hxa : x = a
    · exact ⟨b, fun hxb => hab (hxa.symm.trans hxb)⟩
    · exact ⟨a, hxa⟩
  have hDomain : domain (J : Relation α) = universal := by
    apply classExt
    intro x
    exact ⟨fun _ => trivial, fun _ => everyHasDifferent x⟩
  have hConverse : converseDomain (J : Relation α) = universal := by
    apply classExt
    intro x
    constructor
    · exact fun _ => trivial
    · intro _
      obtain ⟨y, hxy⟩ := everyHasDifferent x
      exact ⟨y, hxy.symm⟩
  refine ⟨hDomain, hConverse, ?_⟩
  apply classExt
  intro x
  exact ⟨fun _ => trivial, fun _ => Or.inl (everyHasDifferent x)⟩

/-- PM I ✱50·34: diversity is inhabited on the type of classes. -/
theorem star_50_34 [Nonempty α] :
    ∃ A B : ClassExtension α, A ≠ B := by
  let ⟨x⟩ := (inferInstance : Nonempty α)
  refine ⟨fun _ => False, fun _ => True, ?_⟩
  intro h
  have point := congrFun h x
  exact Eq.mpr point trivial

end PM.Architecture.Star50OpeningKernel2
