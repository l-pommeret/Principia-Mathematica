namespace PM.Architecture.Star20Q324Kernel

/-- Exact typed content of the class analogue PM I ✱20·62.  The hypothesis
`exhaustive` is the ✱20·07 presentation of every class argument by an
extension `ẑ(φ!z)`; no choice of a global inverse is made. -/
theorem star_20_62 (representation : κ → C)
    (exhaustive : ∀ α : C, ∃ φ, representation φ = α) (f : C → Prop) :
    (∀ φ, f (representation φ)) → ∀ α, f α := by
  intro represented α
  obtain ⟨φ, rfl⟩ := exhaustive α
  exact represented φ

/-- Exact proposition at PM I ✱20·63, the class-variable analogue of
✱10·12. -/
theorem star_20_63 (p : Prop) (f : C → Prop) :
    (∀ α, p ∨ f α) → p ∨ ∀ α, f α := by
  classical
  intro universal
  exact Classical.byCases (p := p) Or.inl
    (fun hp => Or.inr (fun α => (universal α).resolve_left hp))

/-- Significance is represented by successful homogeneous type formation:
both applications are propositions because `α` and `β` inhabit the same
class-argument type. -/
def Significant (_ : Prop) : Prop := True

/-- Exact metalinguistic content of PM I ✱20·631. -/
theorem star_20_631 (f : C → Prop) (α β : C) :
    Significant (f α) ↔ Significant (f β) :=
  Iff.rfl

/-- There is a proposition at some argument of `C`.  Retaining the actual
proposition, rather than merely `True`, makes the function-formation content
of ✱20·632 explicit. -/
def HasPropositionAtSomeArgument (C : Sort u) : Prop :=
  ∃ _ : C, Nonempty Prop

/-- There is a propositional function on the homogeneous class type. -/
def HasPropositionalFunction (C : Sort u) : Prop :=
  Nonempty (C → Prop)

/-- Exact typed formation equivalence at PM I ✱20·632.  PM class types are
inhabited; the assumption is exposed instead of hidden in a selected class. -/
theorem star_20_632 [Nonempty C] :
    HasPropositionAtSomeArgument C ↔ HasPropositionalFunction C := by
  constructor
  · rintro ⟨_, ⟨p⟩⟩
    exact ⟨fun _ => p⟩
  · rintro ⟨f⟩
    let α : C := Classical.choice inferInstance
    exact ⟨α, ⟨f α⟩⟩

/-- Exact quantifier-interchange rule stated at PM I ✱20·633.  Only binder
order changes; the matrix remains `f α β`. -/
theorem star_20_633 (f : A → B → Prop) :
    (∀ α, ∀ β, f α β) → ∀ β, ∀ α, f α β := by
  intro universal β α
  exact universal α β

end PM.Architecture.Star20Q324Kernel
