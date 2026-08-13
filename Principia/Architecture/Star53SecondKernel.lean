import Principia.Architecture.Star53OpeningKernel

namespace PM.Architecture.Star53SecondKernel

open PM.Architecture.Star53OpeningKernel

def diff (a b : Class α) : Class α := fun x => a x ∧ ¬ b x
def empty : Class α := fun _ => False
def emptyRelation : Relation α := fun _ _ => False
def preimage (f : α → β) (b : Class β) : Class α := fun x => b (f x)
def image (f : α → β) (a : Class α) : Class β := fun y => ∃ x, a x ∧ f x = y
def unitClasses : Class (Class α) := fun a => ∃ x, a = singleton x

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x; exact propext (h x)

private theorem relation_ext {r s : Relation α} (h : ∀ x y, r x y ↔ s x y) : r = s := by
  funext x y; exact propext (h x y)

/-- PM I ✱53·16. -/
theorem star_53_16 (k : Class (Relation α)) (r : Relation α) :
    relationProduct (union k (singleton r)) = relationInter (relationProduct k) r := by
  apply relation_ext
  intro x y
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), h r (Or.inr rfl)⟩
  · intro h q hq
    cases hq with
    | inl hk => exact h.1 q hk
    | inr hr => cases hr; exact h.2

/-- PM I ✱53·17. -/
theorem star_53_17 (k : Class (Relation α)) (r : Relation α) :
    relationSum (union k (singleton r)) = relationUnion (relationSum k) r := by
  apply relation_ext
  intro x y
  constructor
  · rintro ⟨q, hq, hxy⟩
    cases hq with
    | inl hk => exact Or.inl ⟨q, hk, hxy⟩
    | inr hr => cases hr; exact Or.inr hxy
  · intro h
    cases h with
    | inl hk => exact ⟨hk.choose, Or.inl hk.choose_spec.1, hk.choose_spec.2⟩
    | inr hr => exact ⟨r, Or.inr rfl, hr⟩

/-- PM I ✱53·18. -/
theorem star_53_18 (k : Class (Class α)) :
    classSum (diff k (singleton empty)) = classSum k := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨a, ⟨ha, _⟩, hx⟩; exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, ⟨ha, ?_⟩, hx⟩
    intro hae
    cases hae
    exact hx

/-- PM I ✱53·181. -/
theorem star_53_181 (k : Class (Relation α)) :
    relationSum (diff k (singleton emptyRelation)) = relationSum k := by
  apply relation_ext
  intro x y
  constructor
  · rintro ⟨r, ⟨hr, _⟩, hxy⟩; exact ⟨r, hr, hxy⟩
  · rintro ⟨r, hr, hxy⟩
    refine ⟨r, ⟨hr, ?_⟩, hxy⟩
    intro hre
    cases hre
    exact hxy

/-- PM I ✱53·2: a one-member class of classes has the same unique member,
product, and sum. -/
theorem star_53_2 (k : Class (Class α)) (a : Class α) (hk : k = singleton a) :
    a = classProduct k ∧ classProduct k = classSum k := by
  subst k
  exact ⟨(star_53_01 a).symm, (star_53_01 a).trans (star_53_02 a).symm⟩

/-- PM I ✱53·21, relation analogue of ✱53·2. -/
theorem star_53_21 (k : Class (Relation α)) (r : Relation α) (hk : k = singleton r) :
    r = relationProduct k ∧ relationProduct k = relationSum k := by
  subst k
  exact ⟨(star_53_03 r).symm, (star_53_03 r).trans (star_53_04 r).symm⟩

/-- PM I ✱53·22. -/
theorem star_53_22 (a : Class α) : classSum (image singleton a) = a := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩; cases hxy; exact hy
  · intro hx; exact ⟨singleton x, ⟨x, hx, rfl⟩, rfl⟩

/-- PM I ✱53·221. -/
theorem star_53_221 (x y : α) :
    image singleton (union (singleton x) (singleton y)) =
      union (singleton (singleton x)) (singleton (singleton y)) := by
  apply class_ext
  intro a
  constructor
  · rintro ⟨z, hz, rfl⟩
    cases hz with
    | inl hx => cases hx; exact Or.inl rfl
    | inr hy => cases hy; exact Or.inr rfl
  · intro h
    cases h with
    | inl hx => cases hx; exact ⟨x, Or.inl rfl, rfl⟩
    | inr hy => cases hy; exact ⟨y, Or.inr rfl, rfl⟩

/-- PM I ✱53·222. -/
theorem star_53_222 (k : Class (Class α)) (a : Class α)
    (hk : k = image singleton a) : a = preimage singleton k := by
  subst k
  apply class_ext
  intro x
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    have : x = y := by
      have hyx : y = x := by
        have hm : singleton x y := by rw [← heq]; rfl
        exact hm
      exact hyx.symm
    cases this
    exact hy

/-- PM I ✱53·23. -/
theorem star_53_23 (k : Class (Class α)) :
    (∀ a, k a → unitClasses a) → classSum k = preimage singleton k := by
  intro hk
  apply class_ext
  intro x
  constructor
  · rintro ⟨a, ha, hx⟩
    rcases hk a ha with ⟨y, rfl⟩
    cases hx
    exact ha
  · intro hx
    exact ⟨singleton x, hx, rfl⟩

end PM.Architecture.Star53SecondKernel
