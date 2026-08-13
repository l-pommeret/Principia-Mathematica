/-! # Principia Mathematica I, ✱95 — equi-factor source model -/
namespace PM.FirstEdition.Volume1.Star95Source

abbrev Rel (α : Sort u) := α → α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z

/-- ✱95·01: the least class containing `R` and closed under `M ↦ P|M|Q`. -/
inductive Equi (P Q R : Rel α) : Rel α → Prop
  | base : Equi P Q R R
  | step {M} : Equi P Q R M → Equi P Q R (comp (comp P M) Q)

end PM.FirstEdition.Volume1.Star95Source
