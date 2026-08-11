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

end PM.FirstEdition.Volume1.Star3
