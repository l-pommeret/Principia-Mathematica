import Principia.Architecture.Star63TypeKernel2

namespace PM.Architecture.Star63TypeKernel3

open PM.Architecture.Star63TypeKernel2

abbrev Class (U : Type u) := U → Prop
def singleton (x : U) : Class U := fun y => y = x
def complement (A : Class U) : Class U := fun x => ¬ A x
def union (A B : Class U) : Class U := fun x => A x ∨ B x
def subset (A B : Class U) : Prop := ∀ ⦃x⦄, A x → B x
def nonempty (A : Class U) : Prop := ∃ x, A x

variable {U : Type u} (r : U → U → Prop)
variable (hr : ∀ x, r x x) (hs : ∀ {x y}, r x y → r y x)
variable (ht : ∀ {x y z}, r x y → r y z → r x z)
include hr hs ht

/-- ✱63·101: the type of `x` is the homogeneous closure of its unit class. -/
theorem star_63_101 (x : U) : t r x = t0 r (singleton x) := by
  funext y; apply propext; constructor
  · intro h; exact ⟨x, rfl, h⟩
  · rintro ⟨z, rfl, h⟩; exact h

/-- ✱63·102: every object belongs to `tʻx` when the ambient simple type is fixed. -/
theorem star_63_102 (hfull : ∀ x y, r x y) (x y : U) : t r x y := hfull y x

/-- ✱63·104. -/
theorem star_63_104 (hfull : ∀ x y, r x y) (φ : U → Prop) {x y : U}
    (_hx : φ x) (_hy : ¬ φ y) : t r x y := hfull y x

/-- ✱63·105: every class is contained in its homogeneous closure. -/
theorem star_63_105 (A : Class U) : subset A (t0 r A) := by
  intro x hx; exact ⟨x, hx, hr x⟩

/-- ✱63·106: a class and its complement have the same type closure in a fixed type. -/
theorem star_63_106 (hfull : ∀ x y, r x y) (A : Class U)
    (hA : nonempty A) (hAc : nonempty (complement A)) : t0 r A = t0 r (complement A) := by
  funext x; apply propext; constructor <;> intro _
  · rcases hAc with ⟨y, hy⟩; exact ⟨y, hy, hfull x y⟩
  · rcases hA with ⟨y, hy⟩; exact ⟨y, hy, hfull x y⟩

/-- ✱63·12: excluded middle characterizes membership in a fixed relative type. -/
theorem star_63_12 (hfull : ∀ x y, r x y) (φ : U → Prop) (x y : U) :
    (φ y ∨ ¬ φ y) ↔ t r x y := ⟨fun _ => hfull y x, fun _ => Classical.em _⟩

/-- ✱63·151: homogeneous closure is idempotent. -/
theorem star_63_151 (A : Class U) : t0 r (t0 r A) = t0 r A := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩; exact ⟨z, hz, ht hxy hyz⟩
  · rintro ⟨y, hy, hxy⟩; exact ⟨x, ⟨y, hy, hxy⟩, hr x⟩

/-- ✱63·152. -/
theorem star_63_152 (x : U) : t0 r (t r x) x := ⟨x, hr x, hr x⟩

/-- ✱63·19: taking the relative type after class closure changes nothing. -/
theorem star_63_19 {A : Class U} {x : U} (hx : A x) (hA : subset A (t r x)) :
    t0 r A = t0 r (t r x) := by
  have h₁ : t0 r A = t r x := by
    funext y; apply propext; constructor
    · rintro ⟨z, hz, hyz⟩; exact ht hyz (hA hz)
    · intro hy; exact ⟨x, hx, hy⟩
  rw [h₁]
  funext y; apply propext; constructor
  · intro hy; exact ⟨x, hr x, hy⟩
  · rintro ⟨z, hz, hyz⟩; exact ht hyz hz

/-- ✱63·191. -/
theorem star_63_191 {A : Class U} {x : U} (hx : A x) :
    t0 r A x := star_63_105 r hr hs ht A hx

/-- ✱63·31: union distributes over homogeneous closure. -/
theorem star_63_31 (A B : Class U) : t0 r (union A B) = union (t0 r A) (t0 r B) := by
  funext x; apply propext; constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

/-- ✱63·32: the first class-type is the closure of the zeroth. -/
theorem star_63_32 (A : Class U) : t0 r (t0 r A) = t0 r A := star_63_151 r hr hs ht A
/-- ✱63·321, retaining both displayed equalities. -/
theorem star_63_321 (A : Class U) :
    t0 r A = t0 r (t0 r A) ∧ t0 r (t0 r A) = t0 r A :=
  ⟨(star_63_151 r hr hs ht A).symm, star_63_151 r hr hs ht A⟩

/-- ✱63·34: both displayed normal forms of a relative type. -/
theorem star_63_34 (x : U) : t0 r (t r x) = t r x ∧ t0 r (t r x) = t0 r (t r x) :=
  ⟨by
    funext y; apply propext; constructor
    · rintro ⟨z, hz, hyz⟩; exact ht hyz hz
    · intro hy; exact ⟨x, hr x, hy⟩, rfl⟩

/-- ✱63·382: the first-order type class exists. -/
theorem star_63_382 (A : Class U) (hne : nonempty A) : nonempty (t0 r A) := by
  rcases hne with ⟨x, hx⟩; exact ⟨x, x, hx, hr x⟩

/-- ✱63·383: the type of a first-order type returns the preceding order. -/
theorem star_63_383 (A : Class U) : t0 r (t0 r A) = t0 r A := star_63_151 r hr hs ht A

end PM.Architecture.Star63TypeKernel3
