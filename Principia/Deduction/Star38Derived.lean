import Principia.Deduction.Star36Derived
import Principia.FirstEdition.Volume1.Star38Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱38 — operations with two descriptors

The 16 catalogue items were audited from `Star38Source`.  Definitions ✱38·01
and ✱38·02 form left and right sections of a two-descriptor operation by
contextual relation abstraction; ✱38·03 then forms their class image.  Such
abstractions and descriptions are intentionally incomplete symbols in
`RamifiedSyntax`, not standalone `Term`s.

Accordingly the first assertions ✱38·1 and ✱38·101 require the absent pure
application/elimination theorem corresponding to ✱21·3.  The image assertions
✱38·13 and ✱38·131 also depend on ✱37·1, whose precise ✱20·3 obstruction is
recorded in `Star37Derived`.  The remaining assertions cite those results and
description/equality rules such as ✱14·21 and ✱30·3 that are not exposed as
ramified `Derivation` theorems.

The host-language `Star38Kernel` represents operations by Lean functions and
uses Lean equality, so importing it would violate the object-language and
purity contract.  No weakened or premise-circular assertion is declared here.
-/

end PM.RamifiedSyntax
