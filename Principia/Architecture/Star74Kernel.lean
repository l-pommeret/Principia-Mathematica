/-!
# PM I ✱74 — one-many and many-one relations with limited fields

Canonical source: Whitehead–Russell, *Principia Mathematica* I (1910),
✱74, pp. 490–499; Project Gutenberg ebook 78050.  The PM restrictions
`R ↾ β` and `β ↿ R` are represented extensionally below.  The central
results ✱74·1, ·11, ·12 and their converse/union duals are kernel proofs.
-/

namespace PM.Architecture.Star74Kernel

abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

def rightRestrict (R : Rel α β) (s : Set β) : Rel α β :=
  fun x y => R x y ∧ s y
def leftRestrict (s : Set α) (R : Rel α β) : Rel α β :=
  fun x y => s x ∧ R x y
def domain (R : Rel α β) : Set α := fun x => ∃ y, R x y
def range (R : Rel α β) : Set β := fun y => ∃ x, R x y
def image (R : Rel α β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ R x y
def preimage (R : Rel α β) (s : Set β) : Set α := fun x => ∃ y, s y ∧ R x y
def subset (s t : Set α) : Prop := ∀ ⦃x⦄, s x → t x
def union (s t : Set α) : Set α := fun x => s x ∨ t x
def InjectiveOn (R : Rel α β) (s : Set α) : Prop :=
  ∀ ⦃x z y⦄, s x → s z → R x y → R z y → x = z
def FunctionalOn (R : Rel α β) (s : Set α) : Prop :=
  ∀ ⦃x y z⦄, s x → R x y → R x z → y = z

/-- ✱74·1: a one-many restriction is injective iff its values separate
members of the restricted class (relational, description-free form). -/
theorem star_74_1 (R : Rel α β) (s : Set α) :
    InjectiveOn R s ↔
      ∀ ⦃x z y⦄, s x → s z → R x y → R z y → x = z := Iff.rfl

/-- ✱74·11: totality on the restricted class is exactly containment in
the domain. -/
theorem star_74_11 (R : Rel α β) (s : Set α) :
    subset s (domain R) ↔ ∀ ⦃x⦄, s x → ∃ y, R x y := Iff.rfl

/-- ✱74·12: injectivity on a limited field, expanded pointwise. -/
theorem star_74_12 (R : Rel α β) (s : Set α) :
    InjectiveOn R s ↔
      ∀ ⦃x z⦄, s x → s z →
        (∃ y, R x y ∧ R z y) → x = z := by
  constructor
  · intro h x z hx hz
    rintro ⟨y, hxy, hzy⟩
    exact h hx hz hxy hzy
  · intro h x z y hx hz hxy hzy
    exact h hx hz ⟨y, hxy, hzy⟩

/-- Limiting a relation does not alter its values inside the limit. -/
theorem star_74_41 (R : Rel α β) (s : Set α) {x : α} (hx : s x) {y : β} :
    leftRestrict s R x y ↔ R x y := by
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- The converse-domain dual of ✱74·41. -/
theorem star_74_411 (R : Rel α β) (s : Set β) {x : α} {y : β} (hy : s y) :
    rightRestrict R s x y ↔ R x y := by
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

/-- ✱74·8: functionality on a union is equivalent to functionality on
each part plus the necessary cross compatibility. -/
theorem star_74_8 (R : Rel α β) (s t : Set α) :
    FunctionalOn R (union s t) ↔
      FunctionalOn R s ∧ FunctionalOn R t ∧
        (∀ ⦃x y z⦄, s x → t x → R x y → R x z → y = z) := by
  constructor
  · intro h
    exact ⟨(fun {_ _ _} hx hxy hxz => h (Or.inl hx) hxy hxz),
      (fun {_ _ _} hx hxy hxz => h (Or.inr hx) hxy hxz),
      (fun {_ _ _} hx _ hxy hxz => h (Or.inl hx) hxy hxz)⟩
  · rintro ⟨hs, ht, _⟩ x y z (hx | hx) hxy hxz
    · exact hs hx hxy hxz
    · exact ht hx hxy hxz

/-- ✱74·801, the many-one (injective) union analogue, including the
cross-disjointness condition which PM's class notation packages. -/
theorem star_74_801 (R : Rel α β) (s t : Set α) :
    InjectiveOn R (union s t) ↔
      InjectiveOn R s ∧ InjectiveOn R t ∧
        (∀ ⦃x z y⦄, s x → t z → R x y → R z y → x = z) ∧
        (∀ ⦃x z y⦄, t x → s z → R x y → R z y → x = z) := by
  constructor
  · intro h
    exact ⟨(fun {_ _ _} hx hz => h (Or.inl hx) (Or.inl hz)),
      (fun {_ _ _} hx hz => h (Or.inr hx) (Or.inr hz)),
      (fun {_ _ _} hx hz => h (Or.inl hx) (Or.inr hz)),
      (fun {_ _ _} hx hz => h (Or.inr hx) (Or.inl hz))⟩
  · rintro ⟨hs, ht, hst, hts⟩ x z y (hx | hx) (hz | hz) hxy hzy
    · exact hs hx hz hxy hzy
    · exact hst hx hz hxy hzy
    · exact hts hx hz hxy hzy
    · exact ht hx hz hxy hzy

/-- Restrictions distribute over a union of limiting classes. -/
theorem star_74_81 (R : Rel α β) (s t : Set α) :
    leftRestrict (union s t) R =
      fun x y => leftRestrict s R x y ∨ leftRestrict t R x y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx | hx, h⟩
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨Or.inl hx, h⟩
    · exact ⟨Or.inr hx, h⟩

/-- Converse restriction dual of ✱74·81. -/
theorem star_74_811 (R : Rel α β) (s t : Set β) :
    rightRestrict R (union s t) =
      fun x y => rightRestrict R s x y ∨ rightRestrict R t x y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h, hy | hy⟩
    · exact Or.inl ⟨h, hy⟩
    · exact Or.inr ⟨h, hy⟩
  · rintro (⟨h, hy⟩ | ⟨h, hy⟩)
    · exact ⟨h, Or.inl hy⟩
    · exact ⟨h, Or.inr hy⟩

end PM.Architecture.Star74Kernel
