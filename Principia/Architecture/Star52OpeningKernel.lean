import Principia.FirstEdition.Volume1.Star52Source

namespace PM.Architecture.Star52OpeningKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def singleton (x : α) : Class α := fun y => y = x
def universalClass (α : Sort u) : Class α := fun _ => True

/-- PM I ✱52·01: the class `1` of unit classes. -/
def unitClasses (α : Sort u) : Class (Class α) :=
  fun A => ∃ x, A = singleton x

/-- The singleton relation `ι`, oriented from unit classes to their members. -/
def iotaRelation : Relation (Class α) α :=
  fun A x => A = singleton x

def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def image (R : Relation α β) (B : Class β) : Class α :=
  fun x => ∃ y, B y ∧ R x y
def converseImage (R : Relation α β) (A : Class α) : Class β :=
  fun y => ∃ x, A x ∧ R x y
def inhabitedClass (A : Class α) : Prop := ∃ x, A x

/-- Exact definitional equation PM I ✱52·01. -/
theorem star_52_01 :
    unitClasses α = (fun A => ∃ x, A = singleton x) := by
  rfl

/-- Exact membership reduction PM I ✱52·1. -/
theorem star_52_1 (A : Class α) :
    unitClasses α A ↔ ∃ x, A = singleton x := by
  rfl

/-- Exact extensional singleton characterization PM I ✱52·11. -/
theorem star_52_11 (A : Class α) :
    unitClasses α A ↔ ∃ x, ∀ y, A y ↔ y = x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun _ => Iff.rfl⟩
  · rintro ⟨x, pointwise⟩
    refine ⟨x, ?_⟩
    funext y
    exact propext (pointwise y)

/-- Exact description-existence characterization PM I ✱52·12. -/
theorem star_52_12 (φ : α → Prop) :
    unitClasses α φ ↔ ∃ x, φ x ∧ ∀ y, φ y → y = x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl, fun y hy => hy⟩
  · rintro ⟨x, member, unique⟩
    refine ⟨x, ?_⟩
    funext y
    apply propext
    exact ⟨fun hy => unique y hy, fun hy => hy ▸ member⟩

/-- Exact identity PM I ✱52·13. -/
theorem star_52_13 :
    unitClasses α = domain (iotaRelation (α := α)) := by
  rfl

/-- Exact image identity PM I ✱52·14. -/
theorem star_52_14 :
    unitClasses α = image (iotaRelation (α := α)) (universalClass α) := by
  funext A
  apply propext
  constructor
  · rintro ⟨x, equality⟩
    exact ⟨x, True.intro, equality⟩
  · rintro ⟨x, _, equality⟩
    exact ⟨x, equality⟩

/-- Exact converse-image existence characterization PM I ✱52·15. -/
theorem star_52_15 (A : Class α) :
    unitClasses α A ↔
      inhabitedClass (converseImage (iotaRelation (α := α))
        (fun candidate => candidate = A)) := by
  constructor
  · rintro ⟨x, equality⟩
    exact ⟨x, A, rfl, equality⟩
  · rintro ⟨x, candidate, candidateEquality, singletonEquality⟩
    exact ⟨x, candidateEquality.symm.trans singletonEquality⟩

/-- Exact non-null-and-unique characterization PM I ✱52·16.  PM's `∃!A`
means that the class `A` is inhabited (✱24·03), not unique existence. -/
theorem star_52_16 (A : Class α) :
    unitClasses α A ↔
      inhabitedClass A ∧ ∀ x y, A x → A y → x = y := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, rfl⟩, fun x y hx hy => hx.trans hy.symm⟩
  · rintro ⟨⟨a, member⟩, unique⟩
    refine ⟨a, ?_⟩
    funext x
    apply propext
    exact ⟨fun hx => unique x a hx member, fun hx => hx ▸ member⟩

end PM.Architecture.Star52OpeningKernel
