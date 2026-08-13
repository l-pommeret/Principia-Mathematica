namespace PM.Architecture.Star71OpeningKernel

universe u v
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop
abbrev Class (α : Sort u) := α → Prop

def rightSection (R : Relation α β) (y : β) : Class α := fun x => R x y
def leftSection (R : Relation α β) (x : α) : Class β := fun y => R x y
def AtMostOne (a : Class α) : Prop := ∀ ⦃x y⦄, a x → a y → x = y
def OneMany (R : Relation α β) : Prop := ∀ ⦃x y z⦄, R x z → R y z → x = y
def ManyOne (R : Relation α β) : Prop := ∀ ⦃x y z⦄, R x y → R x z → y = z
def OneOne (R : Relation α β) : Prop := OneMany R ∧ ManyOne R
def converse (R : Relation α β) : Relation β α := fun y x => R x y
def rightSectionFamily (R : Relation α β) : Class (Class α) :=
  fun a => ∃ y, a = rightSection R y
def leftSectionFamily (R : Relation α β) : Class (Class β) :=
  fun a => ∃ x, a = leftSection R x
def allAtMostOne (F : Class (Class α)) : Prop := ∀ a, F a → AtMostOne a

/-- PM I ✱71·01, simple-type reading of the defining class abstraction. -/
theorem star_71_01 (R : Relation α β) :
    OneMany R ↔ allAtMostOne (rightSectionFamily R) := by
  constructor
  · intro h a ha x y hx hy
    rcases ha with ⟨z, rfl⟩
    exact h hx hy
  · intro h x y z hx hy
    exact h (rightSection R z) ⟨z, rfl⟩ hx hy

/-- PM I ✱71·02. -/
theorem star_71_02 (R : Relation α β) :
    ManyOne R ↔ allAtMostOne (leftSectionFamily R) := by
  constructor
  · intro h a ha y z hy hz
    rcases ha with ⟨x, rfl⟩
    exact h hy hz
  · intro h x y z hy hz
    exact h (leftSection R x) ⟨x, rfl⟩ hy hz

/-- PM I ✱71·03. -/
theorem star_71_03 (R : Relation α β) :
    OneOne R ↔
      allAtMostOne (rightSectionFamily R) ∧ allAtMostOne (leftSectionFamily R) := by
  rw [OneOne, star_71_01, star_71_02]

/-- PM I ✱71·04. -/
theorem star_71_04 (R : Relation α β) : OneOne R ↔ OneMany R ∧ ManyOne R := Iff.rfl

/-- PM I ✱71·1. -/
theorem star_71_1 (R : Relation α β) :
    OneMany R ↔ ∀ y, AtMostOne (rightSection R y) := by
  constructor
  · exact fun h y x z hx hz => h hx hz
  · exact fun h x z y hx hz => h y hx hz

/-- PM I ✱71·101. -/
theorem star_71_101 (R : Relation α β) :
    ManyOne R ↔ ∀ x, AtMostOne (leftSection R x) := by
  constructor
  · exact fun h x y z hy hz => h hy hz
  · exact fun h x y z hy hz => h x hy hz

/-- PM I ✱71·102. -/
theorem star_71_102 (R : Relation α β) :
    OneOne R ↔
      (∀ y, AtMostOne (rightSection R y)) ∧
      (∀ x, AtMostOne (leftSection R x)) := by
  rw [OneOne, star_71_1, star_71_101]

/-- PM I ✱71·103. -/
theorem star_71_103 (R : Relation α β) : OneOne R ↔ OneMany R ∧ ManyOne R := Iff.rfl

/-- PM I ✱71·11. -/
theorem star_71_11 (R : Relation α β) :
    OneMany R ↔ ∀ y, (¬ ∃ x, R x y) ∨ ∃ x, R x y ∧ ∀ z, R z y → z = x := by
  rw [star_71_1]
  constructor
  · intro h y
    classical
    by_cases he : ∃ x, R x y
    · rcases he with ⟨x, hx⟩
      exact Or.inr ⟨x, hx, fun z hz => h y hz hx⟩
    · exact Or.inl he
  · intro h y x z hx hz
    rcases h y with he | ⟨w, hw, hu⟩
    · exact (he ⟨x, hx⟩).elim
    · exact (hu x hx).trans (hu z hz).symm

/-- PM I ✱71·111. -/
theorem star_71_111 (R : Relation α β) :
    ManyOne R ↔ ∀ x, (¬ ∃ y, R x y) ∨ ∃ y, R x y ∧ ∀ z, R x z → z = y := by
  rw [star_71_101]
  constructor
  · intro h x
    classical
    by_cases he : ∃ y, R x y
    · rcases he with ⟨y, hy⟩
      exact Or.inr ⟨y, hy, fun z hz => h x hz hy⟩
    · exact Or.inl he
  · intro h x y z hy hz
    rcases h x with he | ⟨w, hw, hu⟩
    · exact (he ⟨y, hy⟩).elim
    · exact (hu y hy).trans (hu z hz).symm

/-- PM I ✱71·112. -/
theorem star_71_112 (R : Relation α β) : OneOne R ↔
    (∀ y, (¬ ∃ x, R x y) ∨ ∃ x, R x y ∧ ∀ z, R z y → z = x) ∧
    (∀ x, (¬ ∃ y, R x y) ∨ ∃ y, R x y ∧ ∀ z, R x z → z = y) := by
  rw [OneOne, star_71_11, star_71_111]

/-- PM I ✱71·12. -/
theorem star_71_12 (R : Relation α β) :
    OneMany R ↔ ∀ y, AtMostOne (fun x => R x y) := star_71_1 R

/-- PM I ✱71·121. -/
theorem star_71_121 (R : Relation α β) :
    ManyOne R ↔ ∀ x, AtMostOne (fun y => R x y) := star_71_101 R

/-- PM I ✱71·122. -/
theorem star_71_122 (R : Relation α β) : OneOne R ↔
    (∀ y, AtMostOne (fun x => R x y)) ∧ (∀ x, AtMostOne (fun y => R x y)) :=
  star_71_102 R

/-- PM I ✱71·13. -/
theorem star_71_13 (R : Relation α β) :
    OneMany R ↔ ∀ y, AtMostOne (rightSection R y) := star_71_1 R

/-- PM I ✱71·131. -/
theorem star_71_131 (R : Relation α β) :
    ManyOne R ↔ ∀ x, AtMostOne (leftSection R x) := star_71_101 R

/-- PM I ✱71·132. -/
theorem star_71_132 (R : Relation α β) : OneOne R ↔
    (∀ y, AtMostOne (rightSection R y)) ∧
    (∀ x, AtMostOne (leftSection R x)) := star_71_102 R

/-- PM I ✱71·14. -/
theorem star_71_14 (R : Relation α β) :
    OneMany R ↔ ∀ y, (∃ x, R x y) → AtMostOne (rightSection R y) := by
  rw [star_71_1]
  constructor
  · exact fun h y _ => h y
  · intro h y x z hx hz
    exact h y ⟨x, hx⟩ hx hz

/-- PM I ✱71·141. -/
theorem star_71_141 (R : Relation α β) :
    ManyOne R ↔ ∀ x, (∃ y, R x y) → AtMostOne (leftSection R x) := by
  rw [star_71_101]
  constructor
  · exact fun h x _ => h x
  · intro h x y z hy hz
    exact h x ⟨y, hy⟩ hy hz

/-- PM I ✱71·142. -/
theorem star_71_142 (R : Relation α β) : OneOne R ↔
    (∀ y, (∃ x, R x y) → AtMostOne (rightSection R y)) ∧
    (∀ x, (∃ y, R x y) → AtMostOne (leftSection R x)) := by
  rw [OneOne, star_71_14, star_71_141]

/-- PM I ✱71·15. -/
theorem star_71_15 (R : Relation α β) :
    OneMany R ↔ allAtMostOne (rightSectionFamily R) := star_71_01 R

end PM.Architecture.Star71OpeningKernel
