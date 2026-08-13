namespace PM.Architecture.Star63TypeKernel

abbrev Class (U : Type u) := U → Prop
def typeOf (r : U → U → Prop) (x : U) : Class U := fun y => r y x
def subset (A B : Class U) : Prop := ∀ ⦃x⦄, A x → B x
def meet (A B : Class U) : Class U := fun x => A x ∧ B x
def nonempty (A : Class U) : Prop := ∃ x, A x
def closure (r : U → U → Prop) (A : Class U) : Class U :=
  fun z => ∃ y, A y ∧ typeOf r y z

variable {U : Type u} (r : U → U → Prop)
variable (hr : ∀ x, r x x) (hs : ∀ {x y}, r x y → r y x)
variable (ht : ∀ {x y z}, r x y → r y z → r x z)
include hr hs ht

/-- ✱63·103. -/
theorem star_63_103 (x : U) : typeOf r x x := hr x

/-- ✱63·11. -/
theorem star_63_11 {x y : U} (h : typeOf r y x) : typeOf r x = typeOf r y := by
  funext z; apply propext; constructor
  · intro hz; exact ht hz h
  · intro hz; exact ht hz (hs h)

/-- ✱63·13. -/
theorem star_63_13 {x y : U} (h : r x y) : typeOf r x y := hs h

/-- ✱63·16, the membership, intersection, and equality criteria. -/
theorem star_63_16 (x y : U) :
    typeOf r y x ↔ typeOf r x y ∧ nonempty (meet (typeOf r x) (typeOf r y)) ∧
      typeOf r x = typeOf r y := by
  constructor
  · intro h
    exact ⟨hs h, ⟨x, hr x, h⟩, star_63_11 r (hr := hr) (hs := hs) (ht := ht) h⟩
  · rintro ⟨h, _⟩; exact hs h

/-- ✱63·17. -/
theorem star_63_17 {x y z : U} (hy : typeOf r x y) (hz : typeOf r y z) :
    typeOf r x z := ht hz hy

/-- ✱63·18. -/
theorem star_63_18 (x : U) : nonempty (typeOf r x) := ⟨x, hr x⟩

/-- ✱63·181. -/
theorem star_63_181 (x y : U) :
    nonempty (meet (typeOf r x) (typeOf r y)) ↔ typeOf r x = typeOf r y := by
  constructor
  · rintro ⟨z, hx, hy⟩; exact star_63_11 r (hr := hr) (hs := hs) (ht := ht) (ht (hs hx) hy)
  · intro h; exact ⟨x, hr x, h ▸ hr x⟩

/-- ✱63·182. -/
theorem star_63_182 {x y z : U} (hxy : subset (typeOf r x) (typeOf r y))
    (hyz : subset (typeOf r y) (typeOf r z)) : subset (typeOf r x) (typeOf r z) :=
  fun _ h => hyz (hxy h)

/-- ✱63·21. -/
theorem star_63_21 {A : Class U} {x : U} (hne : nonempty A)
    (hA : subset A (typeOf r x)) : closure r A = typeOf r x := by
  funext z; apply propext; constructor
  · rintro ⟨y, hy, hz⟩; exact ht hz (hA hy)
  · intro hz; rcases hne with ⟨y, hy⟩; exact ⟨y, hy, ht hz (hs (hA hy))⟩

/-- ✱63·22. -/
theorem star_63_22 {A : Class U} {x : U} (hx : A x) (hA : subset A (typeOf r x)) :
    closure r A = typeOf r x := star_63_21 r (hr := hr) (hs := hs) (ht := ht) ⟨x, hx⟩ hA

/-- ✱63·371. -/
theorem star_63_371 {A : Class U} {x : U}
    (hhom : ∀ y, A y → typeOf r y = typeOf r x) : subset A (typeOf r x) := by
  intro y hy; rw [← hhom y hy]; exact hr y

/-- ✱63·381. -/
theorem star_63_381 {x y : U} (h : typeOf r x y) : typeOf r y = typeOf r x :=
  star_63_11 r (hr := hr) (hs := hs) (ht := ht) h

/-- ✱63·391. -/
theorem star_63_391 {x y : U} (h : typeOf r x = typeOf r y) :
    closure r (typeOf r x) = closure r (typeOf r y) := congrArg (closure r) h

/-- ✱63·5, characteristic descriptions of a common type. -/
theorem star_63_5 {A : Class U} {x : U} (hx : A x) (hA : subset A (typeOf r x)) :
    typeOf r x x ∧ subset A (typeOf r x) ∧ closure r A = typeOf r x :=
  ⟨hr x, hA, star_63_22 r (hr := hr) (hs := hs) (ht := ht) hx hA⟩

end PM.Architecture.Star63TypeKernel
