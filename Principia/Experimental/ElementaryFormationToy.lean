import Principia.FirstEdition.Volume1.Part1.SectionA.Star2

namespace PM.Experimental.ElementaryFormationToy

open PM
open PM.Elementary
open PM.FirstEdition.Volume1.Star2

/-!
# Extrinsic elementary formation gate for ✱1·7·71·72 and ✱3·03

This experiment keeps the accepted intrinsically typed `PM.Elementary` corpus
unchanged, but refuses to identify syntactic well-typedness with PM's printed
primitive propositions of formation.  `Formation p` is a second, explicit
metalinguistic judgement.  Its two disjunction constructors distinguish a
definite elementary proposition (✱1·71) from an elementary propositional
function with one or more real variables (✱1·72).

The experiment does not claim that this redundant-on-well-typed-terms layer is
the final extrinsic parser for PM.  Its purpose is sharper: it tests whether the
historical formation evidence can be made computationally relevant to the
assertion interface without changing any of the first 85 kernel-checked
derivations or smuggling formation into Lean parameter instantiation.
-/

/-- Explicit evidence that a typed elementary expression was licensed by PM's
formation apparatus.  Only ✱1·71 and ✱1·72 form disjunctions; their context
conditions make the historical distinction observable. -/
inductive Formation : {Γ : PM.RealContext} → PM.Elementary Γ → Prop where
  /-- Primitive elementary constants are admitted by the primitive idea of an
  elementary proposition, not by one of the numbered formation Pp. -/
  | constant (name : String) : Formation (.constant name)
  /-- A real propositional variable is admitted by the primitive idea of an
  elementary propositional function. -/
  | realVar (x : PM.RealVar Γ .elementaryProposition) : Formation (.var x)
  /-- ✱1·7. Negation preserves elementary formation. -/
  | star_1_7 (hp : Formation p) : Formation (∼ₚ p)
  /-- ✱1·71. Disjunction of two definite elementary propositions. -/
  | star_1_71 (hp : Formation (Γ := []) p) (hq : Formation (Γ := []) q) :
      Formation (p ∨ₚ q)
  /-- ✱1·72. Identification of the real-variable type for elementary
  propositional functions.  The same nonempty context is required on both
  sides and is retained in the result. -/
  | star_1_72 (hasRealVariable : Γ ≠ [])
      (hφ : Formation (Γ := Γ) φ) (hψ : Formation (Γ := Γ) ψ) :
      Formation (φ ∨ₚ ψ)

/-- An asserted elementary expression together with the independent evidence
that PM's formation Pp license that expression.  Neither field can be omitted
when constructing a result. -/
structure FormedDerivation {Γ : PM.RealContext} (p : PM.Elementary Γ) : Prop where
  formation : Formation p
  derivation : PM.Derivation p

namespace FormedDerivation

/-- ✱3·01, retained as a definition rather than an equivalence theorem. -/
def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

local infixl:56 " ∧ₑ " => conj

/-- ✱3·03 in the real-variable case.

The `formation` component is built through ✱1·7 and ✱1·72.  The `derivation`
component follows the printed ✱2·11, ✱2·32, ✱1·01, ✱1·11 route.  Consequently
the formation evidence is part of the returned object, not a dead annotation
added solely for dependency metadata. -/
theorem star_3_03 {Γ : PM.RealContext} (hasRealVariable : Γ ≠ [])
    {φ ψ : PM.Elementary Γ}
    (hφ : FormedDerivation φ) (hψ : FormedDerivation ψ) :
    FormedDerivation (φ ∧ₑ ψ) := by
  let notφ : Formation (∼ₚ φ) := Formation.star_1_7 hφ.formation
  let notψ : Formation (∼ₚ ψ) := Formation.star_1_7 hψ.formation
  let joined : Formation (∼ₚ φ ∨ₚ ∼ₚ ψ) :=
    Formation.star_1_72 hasRealVariable notφ notψ
  refine {
    formation := Formation.star_1_7 joined
    derivation := ?_
  }
  let a : PM.Elementary Γ := ∼ₚ φ ∨ₚ ∼ₚ ψ
  have excluded : PM.Derivation (a ∨ₚ ∼ₚ a) := star_2_11 a
  have associated :
      PM.Derivation ((a ∨ₚ ∼ₚ a) ⊃ₚ (∼ₚ φ ∨ₚ (∼ₚ ψ ∨ₚ ∼ₚ a))) :=
    star_2_32 (∼ₚ φ) (∼ₚ ψ) (∼ₚ a)
  have implication : PM.Derivation (φ ⊃ₚ (ψ ⊃ₚ ∼ₚ a)) :=
    PM.Derivation.detach excluded associated
  have afterφ : PM.Derivation (ψ ⊃ₚ ∼ₚ a) :=
    PM.Derivation.detach hφ.derivation implication
  exact PM.Derivation.detach hψ.derivation afterφ

/-- Closed-proposition companion using ✱1·71 rather than ✱1·72.  It is kept
separate so the two printed formation Pp cannot collapse into one generic Lean
constructor. -/
def closedConjunctionFormation {p q : PM.Elementary []}
    (hp : Formation p) (hq : Formation q) : Formation (conj p q) :=
  Formation.star_1_7
    (Formation.star_1_71 (Formation.star_1_7 hp) (Formation.star_1_7 hq))

end FormedDerivation

end PM.Experimental.ElementaryFormationToy
