import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star33Source

namespace PM.RamifiedSyntax

/-!
# PM I, ✱33 — domains

The operators `D`, `ᗡ`, and `C` return classes.  Since class abstractions are
contextual incomplete symbols in `RamifiedSyntax`, they cannot be manufactured
as `Term`s.  The following abbreviations therefore give their eliminable
membership expansions, i.e. the formulae which PM obtains from ✱33·01–·03.
-/

/-- Membership in `DʻR`, the eliminable expansion printed at ✱33·01. -/
def star_33_01
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (applyBinary relation.weaken x.weaken (.apparent .zero))

/-- Membership in `ᗡʻR`, the eliminable expansion printed at ✱33·02. -/
def star_33_02
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (y : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (applyBinary relation.weaken (.apparent .zero) y.weaken)

/-- Membership in `CʻR`, the eliminable expansion printed at ✱33·03. -/
def star_33_03
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  sameDisjunction disjunction
    (star_33_01 existential relation x)
    (star_33_02 existential relation x)

/-- `xFR`, the eliminable expansion printed at ✱33·04. -/
abbrev star_33_04 := @star_33_03

/-!
No derived assertion is declared here.  The first candidates (✱33·1 and
✱33·13) require derivational conversion between a contextual class
abstraction and its membership expansion (✱20·3/·57).  `Derivation` has no
such theorem yet.  Reflexively asserting only the expanded right-hand side
would erase the printed left-hand incomplete symbol and fail the PM AST
contract.
-/

end PM.RamifiedSyntax
