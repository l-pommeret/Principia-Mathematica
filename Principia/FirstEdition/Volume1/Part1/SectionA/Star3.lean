import Principia.Deduction.Formed
import Principia.FirstEdition.Volume1.Part1.SectionA.Star2

namespace PM.Elementary

/-- ✱3·01. Logical product is a definitional abbreviation, not a primitive
connective and not Lean's native conjunction. -/
def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

infixl:56 " ∧ₚ " => conj

/-- ✱3·02. The printed chain is the product of its two adjacent implications;
it is not parsed as a right-associated implication chain. -/
def impChain (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  conj (p ⊃ₚ q) (q ⊃ₚ r)

end PM.Elementary

namespace PM.FirstEdition.Volume1.Star3

open PM
open PM.Elementary

/- PM-VERBATIM-BEGIN PM1:✱3·01
✱3·01.  p . q .=. ∼(∼p ∨ ∼q)     Df
PM-VERBATIM-END PM1:✱3·01 -/

/- PM-VERBATIM-BEGIN PM1:✱3·02
✱3·02.  p ⊃ q ⊃ r .=. p ⊃ q . q ⊃ r     Df
PM-VERBATIM-END PM1:✱3·02 -/

/- PM-FORMAL-GLOSS
The dot between p and q in ✱3·01 is the newly defined logical product. In
✱3·02 the two dots on the right delimit the product of the adjacent
implications. Neither definition is an asserted equivalence proposition.
-/

def star_3_01_printed : PM.PrintedFormula :=
  PM.pmPrinted "p . q .=. ∼(∼p ∨ ∼q)     Df"

def star_3_02_printed : PM.PrintedFormula :=
  PM.pmPrinted "p ⊃ q ⊃ r .=. p ⊃ q . q ⊃ r     Df"

/- PM-VERBATIM-BEGIN PM1:✱3·03
✱3·03. Given two asserted elementary propositional functions “⊢ . φp” and
“⊢ . ψp” whose arguments are elementary propositions, we have ⊢ . φp . ψp.

Dem.

⊢ . ✱1·7·72 . ✱2·11 . ⊃ ⊢ : ∼φp ∨ ∼ψp . ∨ . ∼(∼φp ∨ ∼ψp)              (1)
⊢ . (1) . ✱2·32 . (✱1·01) . ⊃ ⊢ : φp . ⊃ : ψp . ⊃ . ∼(∼φp ∨ ∼ψp)      (2)
⊢ . (2) . (✱3·03) . ⊃ ⊢ : φp . ⊃ : ψp . ⊃ . φp . ψp                   (3)
⊢ . (3) . ✱1·11 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·03 -/

/- PM-EDITORIAL
The canonical first-edition scan prints `(✱3·03)` in the third line of the
demonstration, a circular self-reference. The formula and the preceding
explanation require the definition ✱3·01; the likely correction is therefore
`(✱3·01)`, but the diplomatic bytes above retain the print. This locus remains
classified as an uncertain apparent print error pending a second physical
witness. Project Gutenberg repeats the circular reference and independently
corrupts some φ/ψ glyphs, so it cannot establish an authorial correction.

Sources: printed pp. 114 and 116, scan leaves 136 and 138:
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/136
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/138
-/

/-- ✱3·03. Formation-aware product of two asserted elementary propositional
functions with the same nonempty real-variable context.

The returned object makes the printed formation Pp ✱1·7/✱1·72 operational;
its derivation component follows the displayed ✱2·11, ✱2·32, ✱1·01 and
✱1·11 route. -/
theorem star_3_03 {Γ : PM.RealContext} (hasRealVariable : Γ ≠ [])
    {φ ψ : PM.Elementary Γ}
    (hφ : PM.FormedDerivation φ) (hψ : PM.FormedDerivation ψ) :
    PM.FormedDerivation (PM.Elementary.conj φ ψ) := by
  refine ⟨?_, ?_⟩
  · exact PM.Formation.star_1_7
      (PM.Formation.star_1_72 hasRealVariable
        (PM.Formation.star_1_7 hφ.formation)
        (PM.Formation.star_1_7 hψ.formation))
  · have h1 : ⊢ₚ ((∼ₚ φ ∨ₚ ∼ₚ ψ) ∨ₚ ∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)) :=
      PM.FirstEdition.Volume1.Star2.star_2_11 (∼ₚ φ ∨ₚ ∼ₚ ψ)
    have h2 : ⊢ₚ (φ ⊃ₚ (ψ ⊃ₚ PM.Elementary.conj φ ψ)) :=
      PM.Derivation.star_1_11 hasRealVariable h1
        (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ φ) (∼ₚ ψ)
          (∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)))
    exact PM.Derivation.star_1_11 hasRealVariable hψ.derivation
      (PM.Derivation.star_1_11 hasRealVariable hφ.derivation h2)

end PM.FirstEdition.Volume1.Star3
