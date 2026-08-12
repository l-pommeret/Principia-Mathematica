/-!
Exact contextual-description kernels for PM I, Q299 (✱14·1, ✱14·101,
✱14·11, ✱14·111, and ✱14·112).

Russellian descriptions are not represented as terms here.  The only objects
defined below are the propositional scopes licensed by ✱14·01--04: existence
of a candidate characterized uniquely by its defining predicate, conjoined
with the continuation at that candidate.
-/

namespace PM.Architecture.Star14Q299Kernel

universe u v

/-- The matrix `φx ≡ₓ x = b` occurring in PM's description definitions. -/
def Characterizes (φ : α → Prop) (b : α) : Prop :=
  ∀ x, φ x ↔ x = b

/-- The contextual definiens of `[(℩x)(φx)] . ψ(℩x)(φx)` (✱14·01). -/
def DescriptionScope (φ ψ : α → Prop) : Prop :=
  ∃ b, Characterizes φ b ∧ ψ b

/-- The definiens of `E!(℩x)(φx)` (✱14·02). -/
def DescriptionExists (φ : α → Prop) : Prop :=
  ∃ b, Characterizes φ b

/-- The nested two-description scope licensed by ✱14·03--04. -/
def DescriptionScopePair (φ : α → Prop) (ψ : β → Prop)
    (f : α → β → Prop) : Prop :=
  ∃ b c, Characterizes φ b ∧ Characterizes ψ c ∧ f b c

/-- PM I ✱14·1: explicit description scope elimination. -/
theorem star_14_1 (φ ψ : α → Prop) :
    DescriptionScope φ ψ ↔
      ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := by
  rfl

/-- PM I ✱14·101: the conventionally default description scope. -/
theorem star_14_101 (φ ψ : α → Prop) :
    DescriptionScope φ ψ ↔
      ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := by
  exact star_14_1 φ ψ

/-- PM I ✱14·11: existence of a description is unique characterization. -/
theorem star_14_11 (φ : α → Prop) :
    DescriptionExists φ ↔ ∃ b, ∀ x, φ x ↔ x = b := by
  rfl

/-- PM I ✱14·111: eliminate the later-scoped member of a pair of
descriptions, retaining the complete nested two-candidate definiens. -/
theorem star_14_111 (φ : α → Prop) (ψ : β → Prop)
    (f : α → β → Prop) :
    DescriptionScopePair φ ψ f ↔
      ∃ b c, (∀ x, φ x ↔ x = b) ∧
        (∀ x, ψ x ↔ x = c) ∧ f b c := by
  rfl

/-- PM I ✱14·112: the default scope has the same complete two-description
definiens as ✱14·111. -/
theorem star_14_112 (φ : α → Prop) (ψ : β → Prop)
    (f : α → β → Prop) :
    DescriptionScopePair φ ψ f ↔
      ∃ b c, (∀ x, φ x ↔ x = b) ∧
        (∀ x, ψ x ↔ x = c) ∧ f b c := by
  exact star_14_111 φ ψ f

end PM.Architecture.Star14Q299Kernel
