import Principia.Deduction.System

/-!
# Printed abbreviated titles

PM gives a handful of propositions an abbreviated title and then cites them by
that title inside its demonstrations: the demonstration of ✱2·01 opens with
`[Taut  ∼p/p]`, not with `[✱1·2]`.  Reproducing those titles lets a Lean proof
be read against the printed page name for name.

The list is deliberately exactly the one PM prints.  ✱1·2 (p. 96) says: "It is
called the 'principle of tautology,' and will be quoted by the abbreviated title
of 'Taut.'  It is convenient, for purposes of reference, to give names to a few
of the more important propositions; in general, propositions will be referred to
by their numbers."  No title is invented here for a proposition PM leaves
numbered.

These are abbreviations, not new content: each is definitionally the numbered
proposition it names, so using one is using that proposition, and
`scripts/verify_printed_citations.py` resolves the title back to its number.
-/

namespace PM.Derivation

/-- `Taut`, the principle of tautology: ✱1·2, PM I p. 96. -/
abbrev Taut {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    PM.Derivation ((p ∨ₚ p) ⊃ₚ p) := PM.Derivation.star_1_2 p

/-- `Add`, the principle of addition: ✱1·3, PM I p. 96. -/
abbrev Add {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    PM.Derivation (q ⊃ₚ (p ∨ₚ q)) := PM.Derivation.star_1_3 p q

/-- `Perm`, the principle of permutation: ✱1·4, PM I p. 96. -/
abbrev Perm {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    PM.Derivation ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) := PM.Derivation.star_1_4 p q

/-- `Assoc`, the associative principle: ✱1·5, PM I p. 97. -/
abbrev Assoc {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    PM.Derivation ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_5 p q r

/-- `Sum`, the principle of summation: ✱1·6, PM I p. 97. -/
abbrev Sum {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    PM.Derivation ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_6 p q r

end PM.Derivation
