namespace PM.Architecture.Star51OpeningKernel

abbrev Class (α : Type u) := α → Prop

def singleton (x : α) : Class α := fun y => y = x
def identityImage (x : α) : Class α := fun y => y = x
def iotaRelation (A : Class α) (x : α) : Prop := A = singleton x
def identityImageRelation (A : Class α) (x : α) : Prop := A = identityImage x
def ClassExists (A : Class α) : Prop := ∃ y, A y

/-- ✱51·01. `ι = I⃗` Df. -/
def star_51_01 : Class α → α → Prop := identityImageRelation

/-- ✱51·1: `A ι x` iff `A` is the class of terms identical with `x`. -/
theorem star_51_1 (A : Class α) (x : α) :
    iotaRelation A x ↔ A = (fun y => y = x) := by
  rfl

/-- ✱51·11: the value `ιʻx` is the class abstraction `ŷ(y=x)`. -/
theorem star_51_11 (x : α) : singleton x = (fun y => y = x) := by
  rfl

/-- ✱51·12: the unit-class descriptive-function value exists. -/
theorem star_51_12 (x : α) : ∃ A : Class α, A = singleton x := by
  exact ⟨singleton x, rfl⟩

/-- ✱51·13: equality to `ιʻx` has the displayed abstraction reading. -/
theorem star_51_13 (A : Class α) (x : α) :
    A = singleton x ↔ A = (fun y => y = x) := by
  rfl

/-- ✱51·131: the relational and descriptive-function readings agree. -/
theorem star_51_131 (A : Class α) (x : α) :
    iotaRelation A x ↔ A = singleton x := by
  rfl

/-- ✱51·14: equality to a unit class is pointwise identity membership. -/
theorem star_51_14 (A : Class α) (x : α) :
    A = singleton x ↔ ∀ y, A y ↔ y = x := by
  constructor
  · rintro rfl y
    rfl
  · intro h
    funext y
    exact propext (h y)

/-- ✱51·141: the unit-class characterization by existence and uniqueness,
and equivalently by membership of `x` plus uniqueness. -/
theorem star_51_141 (A : Class α) (x : α) :
    (A = singleton x ↔
      (ClassExists A ∧ ∀ y, A y → y = x)) ∧
    ((ClassExists A ∧ ∀ y, A y → y = x) ↔
      (A x ∧ ∀ y, A y → y = x)) := by
  constructor
  · constructor
    · rintro rfl
      exact ⟨⟨x, rfl⟩, fun _ h => h⟩
    · rintro ⟨⟨y, hy⟩, unique⟩
      have hyx : y = x := unique y hy
      funext z
      apply propext
      exact ⟨unique z, fun hzx => hzx ▸ hyx ▸ hy⟩
  · constructor
    · rintro ⟨⟨y, hy⟩, unique⟩
      have hyx : y = x := unique y hy
      exact ⟨hyx ▸ hy, unique⟩
    · rintro ⟨hx, unique⟩
      exact ⟨⟨x, hx⟩, unique⟩

/-- ✱51·15: membership in `ιʻx` is identity with `x`. -/
theorem star_51_15 (x y : α) : singleton x y ↔ y = x := by
  rfl

/-- ✱51·16: `x` belongs to its own unit class. -/
theorem star_51_16 (x : α) : singleton x x := by
  rfl

end PM.Architecture.Star51OpeningKernel
