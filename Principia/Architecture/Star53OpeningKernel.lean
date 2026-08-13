namespace PM.Architecture.Star53OpeningKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) := α → α → Prop

def singleton (a : α) : Class α := fun x => x = a
def union (a b : Class α) : Class α := fun x => a x ∨ b x
def inter (a b : Class α) : Class α := fun x => a x ∧ b x
def classSum (k : Class (Class α)) : Class α := fun x => ∃ a, k a ∧ a x
def classProduct (k : Class (Class α)) : Class α := fun x => ∀ a, k a → a x
def relationSum (k : Class (Relation α)) : Relation α := fun x y => ∃ r, k r ∧ r x y
def relationProduct (k : Class (Relation α)) : Relation α := fun x y => ∀ r, k r → r x y
def relationUnion (r s : Relation α) : Relation α := fun x y => r x y ∨ s x y
def relationInter (r s : Relation α) : Relation α := fun x y => r x y ∧ s x y

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x; exact propext (h x)

private theorem relation_ext {r s : Relation α} (h : ∀ x y, r x y ↔ s x y) : r = s := by
  funext x y; exact propext (h x y)

/-- PM I ✱53·01. -/
theorem star_53_01 (a : Class α) : classProduct (singleton a) = a := by
  apply class_ext
  intro x
  constructor
  · intro h; exact h a rfl
  · intro hx b hb; cases hb; exact hx

/-- PM I ✱53·02. -/
theorem star_53_02 (a : Class α) : classSum (singleton a) = a := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨b, rfl, hx⟩; exact hx
  · intro hx; exact ⟨a, rfl, hx⟩

/-- PM I ✱53·03. -/
theorem star_53_03 (r : Relation α) : relationProduct (singleton r) = r := by
  apply relation_ext
  intro x y
  constructor
  · intro h; exact h r rfl
  · intro h q hq; cases hq; exact h

/-- PM I ✱53·04. -/
theorem star_53_04 (r : Relation α) : relationSum (singleton r) = r := by
  apply relation_ext
  intro x y
  constructor
  · rintro ⟨q, rfl, h⟩; exact h
  · intro h; exact ⟨r, rfl, h⟩

/-- PM I ✱53·1. -/
theorem star_53_1 (a b : Class α) :
    classProduct (union (singleton a) (singleton b)) = inter a b := by
  apply class_ext
  intro x
  constructor
  · intro h; exact ⟨h a (Or.inl rfl), h b (Or.inr rfl)⟩
  · intro h c hc
    cases hc with
    | inl ha => cases ha; exact h.1
    | inr hb => cases hb; exact h.2

/-- PM I ✱53·11. -/
theorem star_53_11 (a b : Class α) :
    classSum (union (singleton a) (singleton b)) = union a b := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨c, hc, hx⟩
    cases hc with
    | inl ha => cases ha; exact Or.inl hx
    | inr hb => cases hb; exact Or.inr hx
  · intro h
    cases h with
    | inl ha => exact ⟨a, Or.inl rfl, ha⟩
    | inr hb => exact ⟨b, Or.inr rfl, hb⟩

/-- PM I ✱53·12. -/
theorem star_53_12 (r s : Relation α) :
    relationProduct (union (singleton r) (singleton s)) = relationInter r s := by
  apply relation_ext
  intro x y
  constructor
  · intro h; exact ⟨h r (Or.inl rfl), h s (Or.inr rfl)⟩
  · intro h q hq
    cases hq with
    | inl hr => cases hr; exact h.1
    | inr hs => cases hs; exact h.2

/-- PM I ✱53·13. -/
theorem star_53_13 (r s : Relation α) :
    relationSum (union (singleton r) (singleton s)) = relationUnion r s := by
  apply relation_ext
  intro x y
  constructor
  · rintro ⟨q, hq, hxy⟩
    cases hq with
    | inl hr => cases hr; exact Or.inl hxy
    | inr hs => cases hs; exact Or.inr hxy
  · intro h
    cases h with
    | inl hr => exact ⟨r, Or.inl rfl, hr⟩
    | inr hs => exact ⟨s, Or.inr rfl, hs⟩

/-- PM I ✱53·14. -/
theorem star_53_14 (k : Class (Class α)) (a : Class α) :
    classProduct (union k (singleton a)) = inter (classProduct k) a := by
  apply class_ext
  intro x
  constructor
  · intro h; exact ⟨fun b hb => h b (Or.inl hb), h a (Or.inr rfl)⟩
  · intro h b hb
    cases hb with
    | inl hk => exact h.1 b hk
    | inr ha => cases ha; exact h.2

/-- PM I ✱53·15. -/
theorem star_53_15 (k : Class (Class α)) (a : Class α) :
    classSum (union k (singleton a)) = union (classSum k) a := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨b, hb, hx⟩
    cases hb with
    | inl hk => exact Or.inl ⟨b, hk, hx⟩
    | inr ha => cases ha; exact Or.inr hx
  · intro h
    cases h with
    | inl hk => exact ⟨hk.choose, Or.inl hk.choose_spec.1, hk.choose_spec.2⟩
    | inr ha => exact ⟨a, Or.inr rfl, ha⟩

end PM.Architecture.Star53OpeningKernel
