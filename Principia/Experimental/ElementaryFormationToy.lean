import Principia.Deduction.Formed
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

/-- Compatibility projection for the accepted elementary calculus.  The old
API still returns `PM.Derivation`, but its implementation now factors through
the formation-aware ✱3·03 object.  Thus downstream ✱3–✱5 proofs need not be
rewritten merely to carry a second field, while the historical formation proof
remains a real dependency of this bridge. -/
theorem star_3_03_derivation {Γ : PM.RealContext} (hasRealVariable : Γ ≠ [])
    {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hψ : PM.Derivation ψ) :
    PM.Derivation (φ ∧ₑ ψ) :=
  (star_3_03 hasRealVariable
    { formation := Formation.ofElementary φ, derivation := hφ }
    { formation := Formation.ofElementary ψ, derivation := hψ }).derivation

/-- Closed-proposition companion using ✱1·71 rather than ✱1·72.  It is kept
separate so the two printed formation Pp cannot collapse into one generic Lean
constructor. -/
def closedConjunctionFormation {p q : PM.Elementary []}
    (hp : Formation p) (hq : Formation q) : Formation (conj p q) :=
  Formation.star_1_7
    (Formation.star_1_71 (Formation.star_1_7 hp) (Formation.star_1_7 hq))

end FormedDerivation

end PM.Experimental.ElementaryFormationToy
