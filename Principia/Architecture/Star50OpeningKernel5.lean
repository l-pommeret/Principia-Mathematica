namespace PM.Architecture.Star50OpeningKernel5

universe u
abbrev Relation (α : Sort u) := α → α → Prop
abbrev ClassExtension (α : Sort u) := α → Prop
def I : Relation α := fun x y => x = y
def comp (R S : Relation α) : Relation α := fun x z => ∃ y, R x y ∧ S y z
def rightRestrict (R : Relation α) (A : ClassExtension α) : Relation α :=
  fun x y => R x y ∧ A y
def leftRestrict (A : ClassExtension α) (R : Relation α) : Relation α :=
  fun x y => A x ∧ R x y
def domain (R : Relation α) : ClassExtension α := fun x => ∃ y, R x y
def converseDomain (R : Relation α) : ClassExtension α := fun y => ∃ x, R x y
def field (R : Relation α) : ClassExtension α :=
  fun x => domain R x ∨ converseDomain R x
def IncludedC (A B : ClassExtension α) : Prop := ∀ x, A x → B x
def rightMul (R : Relation α) : Relation α → Relation α := fun Q => comp R Q
def leftMul (R : Relation α) : Relation α → Relation α := fun Q => comp Q R

private theorem relationExt {R S : Relation α} (h : ∀ x y, R x y ↔ S x y) :
    R = S := by funext x y; exact propext (h x y)

/-- PM I ✱50·6. -/
theorem star_50_6 (R : Relation α) (A : ClassExtension α) :
    comp R (rightRestrict I A) = rightRestrict R A := by
  apply relationExt; intro x z; constructor
  · rintro ⟨y, hR, hyz, hA⟩; subst z; exact ⟨hR, hA⟩
  · rintro ⟨hR, hA⟩; exact ⟨z, hR, rfl, hA⟩

/-- PM I ✱50·61. -/
theorem star_50_61 (R : Relation α) (A : ClassExtension α) :
    comp (rightRestrict I A) R = leftRestrict A R := by
  apply relationExt; intro x z; constructor
  · rintro ⟨y, ⟨hxy, hA⟩, hR⟩; subst y; exact ⟨hA, hR⟩
  · rintro ⟨hA, hR⟩; exact ⟨x, ⟨rfl, hA⟩, hR⟩

/-- PM I ✱50·62. -/
theorem star_50_62 (R : Relation α) (A : ClassExtension α)
    (h : IncludedC (converseDomain R) A) :
    comp R (rightRestrict I A) = R := by
  rw [star_50_6]
  apply relationExt; intro x y; constructor
  · exact And.left
  · intro hR; exact ⟨hR, h y ⟨x, hR⟩⟩

/-- PM I ✱50·63. -/
theorem star_50_63 (R : Relation α) (A : ClassExtension α)
    (h : IncludedC (domain R) A) :
    comp (rightRestrict I A) R = R := by
  rw [star_50_61]
  apply relationExt; intro x y; constructor
  · exact And.right
  · intro hR; exact ⟨h x ⟨y, hR⟩, hR⟩

/-- PM I ✱50·64. -/
theorem star_50_64 (R : Relation α) :
    comp R (rightRestrict I (converseDomain R)) = R ∧
    comp R (rightRestrict I (field R)) = R := by
  exact ⟨star_50_62 R _ (fun _ h => h),
    star_50_62 R _ (fun _ h => Or.inr h)⟩

/-- PM I ✱50·65. -/
theorem star_50_65 (R : Relation α) :
    comp (rightRestrict I (domain R)) R = R ∧
    comp (rightRestrict I (field R)) R = R := by
  exact ⟨star_50_63 R _ (fun _ h => h),
    star_50_63 R _ (fun _ h => Or.inl h)⟩

/-- PM I ✱50·7. -/
theorem star_50_7 (R : Relation α) (A : ClassExtension α)
    (h : IncludedC (converseDomain R) A) :
    rightMul R (rightRestrict I A) = R := star_50_62 R A h

/-- PM I ✱50·71. -/
theorem star_50_71 (R : Relation α) (A : ClassExtension α)
    (h : IncludedC (domain R) A) :
    leftMul R (rightRestrict I A) = R := star_50_63 R A h

/-- PM I ✱50·72. -/
theorem star_50_72 (R : Relation α) :
    rightMul R (rightRestrict I (field R)) = R ∧
    leftMul R (rightRestrict I (field R)) = R :=
  ⟨(star_50_64 R).2, (star_50_65 R).2⟩

/-- PM I ✱50·73. -/
theorem star_50_73 (R : Relation α) :
    rightMul R I = R ∧ leftMul R I = R := by
  constructor <;> apply relationExt <;> intro x z <;> constructor
  · rintro ⟨y, hR, hyz⟩; subst z; exact hR
  · intro hR; exact ⟨z, hR, rfl⟩
  · rintro ⟨y, hxy, hR⟩; subst y; exact hR
  · intro hR; exact ⟨x, rfl, hR⟩

/-- PM I ✱50·74. -/
theorem star_50_74 (R : Relation α) :
    rightMul (comp R I) = rightMul R :=
  congrArg rightMul (star_50_73 R).1

/-- PM I ✱50·75. -/
theorem star_50_75 (R : Relation α) :
    leftMul (comp I R) = leftMul R :=
  congrArg leftMul (star_50_73 R).2

/-- PM I ✱50·76. -/
theorem star_50_76 (P R : Relation α) : rightMul P = rightMul R ↔ P = R := by
  constructor
  · intro h
    have := congrFun h I
    exact (star_50_73 P).1.symm.trans (this.trans (star_50_73 R).1)
  · intro h; cases h; rfl

/-- PM I ✱50·761. -/
theorem star_50_761 (P R : Relation α) : leftMul P = leftMul R ↔ P = R := by
  constructor
  · intro h
    have := congrFun h I
    exact (star_50_73 P).2.symm.trans (this.trans (star_50_73 R).2)
  · intro h; cases h; rfl

end PM.Architecture.Star50OpeningKernel5
