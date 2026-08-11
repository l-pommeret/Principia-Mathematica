import Principia.Syntax.Description

namespace PM.FirstEdition.Volume1.Star14

/-!
# ✱14. DESCRIPTIONS.

Source: *Principia Mathematica*, first edition, volume I (1910), printed
p. 181, scan leaf 203.

A description is a phrase of the form “the term which etc.,” or, more
explicitly, “the term x which satisfies φx,” where φx is some function
satisfied by one and only one argument. For reasons explained in the
Introduction (Chapter III), we do not define “the x which satisfies φx,” but
we define any proposition in which this phrase occurs.

The proposition which is to be treated as the “ψ(℩x)(φx)” will be called the
scope of `(℩x)(φx)`. In order to avoid ambiguities as to scope, PM indicates
the scope by writing `[(℩x)(φx)]` at its beginning, followed by enough dots to
extend to the end of the scope.

The following is a diplomatic Unicode transcription of the printed
definition.  It is source evidence only.  The canonical target
`PM.DescriptionSyntax.Formula.star_14_01` is deliberately absent pending its
isolated Aristotle body and one-to-one remap.
-/

/- PM-VERBATIM-BEGIN PM1:✱14·01
✱14·01.  [(℩x)(φx)] . ψ(℩x)(φx) .=: (∃b) : φx .≡ₓ. x = b : ψb  Df
PM-VERBATIM-END PM1:✱14·01 -/

end PM.FirstEdition.Volume1.Star14
