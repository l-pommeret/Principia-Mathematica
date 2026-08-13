namespace PM.Architecture.Star33DomainKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def Included (a b : Class α) : Prop := ∀ x, a x → b x
def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def ConverseDomain (R : Relation α β) : Class β := fun y => ∃ x, R x y
def Field (R : Relation α α) : Class α :=
  fun x => (∃ y, R x y) ∨ ∃ y, R y x
def ForwardSection (R : Relation α β) (y : β) : Class α := fun x => R x y
def BackwardSection (R : Relation α β) (x : α) : Class β := fun y => R x y

/-- PM I ✱33·13. -/
theorem star_33_13 (R : Relation α β) (x : α) :
    Domain R x ↔ ∃ y, R x y := Iff.rfl

/-- PM I ✱33·131. -/
theorem star_33_131 (R : Relation α β) (y : β) :
    ConverseDomain R y ↔ ∃ x, R x y := Iff.rfl

/-- PM I ✱33·132. -/
theorem star_33_132 (R : Relation α α) (x : α) :
    Field R x ↔ (∃ y, R x y) ∨ ∃ y, R y x := Iff.rfl

/-- PM I ✱33·14. -/
theorem star_33_14 (R : Relation α β) (x : α) (y : β) :
    R x y → Domain R x ∧ ConverseDomain R y := by
  intro h
  exact ⟨⟨y, h⟩, ⟨x, h⟩⟩

/-- PM I ✱33·15. -/
theorem star_33_15 (R : Relation α β) (y : β) :
    Included (ForwardSection R y) (Domain R) := by
  intro x h
  exact ⟨y, h⟩

/-- PM I ✱33·151. -/
theorem star_33_151 (R : Relation α β) (x : α) :
    Included (BackwardSection R x) (ConverseDomain R) := by
  intro y h
  exact ⟨x, h⟩

/-- PM I ✱33·152. -/
theorem star_33_152 (R : Relation α α) (x : α) :
    Included (Union (ForwardSection R x) (BackwardSection R x)) (Field R) := by
  intro y h
  cases h with
  | inl hyx => exact Or.inl ⟨x, hyx⟩
  | inr hxy => exact Or.inr ⟨x, hxy⟩

/-- PM I ✱33·16. -/
theorem star_33_16 (R : Relation α α) :
    Field R = Union (Domain R) (ConverseDomain R) := rfl

/-- PM I ✱33·161. -/
theorem star_33_161 (R : Relation α α) :
    Included (Domain R) (Field R) ∧ Included (ConverseDomain R) (Field R) := by
  constructor
  · intro x hx
    exact Or.inl hx
  · intro x hx
    exact Or.inr hx

end PM.Architecture.Star33DomainKernel
