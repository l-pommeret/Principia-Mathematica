import Principia.Deduction.Star4Ramified

/-!
# Derivational scope bridges for PM I, ✱9

The printed clauses ✱9·01--·06 are `Df` clauses (`.=.` / `:=.`), not
asserted object-language equivalences.  This file investigates the stronger
judgement-level statements without identifying their independently built
`Formula` trees.
-/

namespace PM.RamifiedSyntax

private theorem scopeBridgeDetach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ q := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction line1 line2
  | cons head tail =>
      exact Derivation.star_1_11_same negation disjunction line1 line2

/-- The judgement-level bridge corresponding to ✱9·02.  Unfolding only
`Formula.sometimes` and `star_9_02` exposes the genuine pair
`∼∼(x).∼φx` and `(x).∼φx`; the two implications are ✱2·14 and ✱2·12,
packaged as an equivalence by ✱3·2. -/
theorem scope_bridge_star_9_02
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (outerDisjunction : signature.Disjunction
      (bindOrder matrixOrder argument))
    (body : Formula signature real [argument] matrixOrder) :
    ⊢ᵣ star_4_01 existential.outerNegation outerDisjunction
      (Formula.neg existential.outerNegation
        (.sometimes existential body))
      (star_9_02 existential.universal existential.matrixNegation body) := by
  let scopedNegation : Formula signature real []
      (bindOrder matrixOrder argument) :=
    .always existential.universal
      (.neg existential.matrixNegation body)
  change ⊢ᵣ star_4_01 existential.outerNegation outerDisjunction
    (.neg existential.outerNegation
      (.neg existential.outerNegation scopedNegation))
    scopedNegation
  have line1 := star_2_14 existential.outerNegation outerDisjunction
    scopedNegation
  have line2 := star_2_12 existential.outerNegation outerDisjunction
    scopedNegation
  have line3 := star_3_2 existential.outerNegation outerDisjunction
    (implication existential.outerNegation outerDisjunction
      (.neg existential.outerNegation
        (.neg existential.outerNegation scopedNegation))
      scopedNegation)
    (implication existential.outerNegation outerDisjunction scopedNegation
      (.neg existential.outerNegation
        (.neg existential.outerNegation scopedNegation)))
  have line4 := scopeBridgeDetach existential.outerNegation outerDisjunction
    _ _ line1 line3
  exact scopeBridgeDetach existential.outerNegation outerDisjunction _ _
    line2 line4

/-
The same construction cannot be repeated for the other five clauses with
the current `Derivation` interface.  After transparent unfolding, their two
members first differ at the following constructor positions:

* ✱9·01: beneath the common `neg (always ...)` prefix, `body` versus
  `neg matrixNegation (neg matrixNegation body)`;
* ✱9·03 and ✱9·04: an outer `Formula.disj` versus `Formula.always`;
* ✱9·05 and ✱9·06: an outer `Formula.disj` versus the `Formula.neg` root
  contributed by `Formula.sometimes`.

Thus ✱9·01 needs congruence of `Formula.always` under the already derivable
double-negation equivalence, while ✱9·03--·06 need the closed-member scope
transport between an external disjunction and a disjunction below a binder.
The quantifier constructors only introduce `Formula.always`, specialize it,
or introduce `Formula.sometimes`; none converts either of those judgement
shapes.  No equality or reflexive surrogate is installed here.
-/

#print axioms scope_bridge_star_9_02

end PM.RamifiedSyntax
