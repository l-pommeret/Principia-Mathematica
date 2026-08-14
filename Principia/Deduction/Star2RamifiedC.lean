import Principia.Deduction.Star2Ramified

namespace PM.RamifiedSyntax

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:max "∼ᵣ" => Formula.neg negation
local infixr:55 " ∨ᵣ " => sameDisjunction disjunction
local infixr:54 " ⊃ᵣ " => implication negation disjunction

-- ✱2·521 is derived in `Star2Ramified`, by the printed ✱2·52·17 route: ✱2·52,
-- then ✱2·17, composed by Syll. It was written here in parallel and the two
-- proofs came out identical, so the duplicate is dropped rather than kept under
-- a second name — the audit below is what this module is for.
#print axioms star_2_521

end

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_2_47
#print axioms PM.RamifiedSyntax.star_2_48
#print axioms PM.RamifiedSyntax.star_2_5
#print axioms PM.RamifiedSyntax.star_2_51
#print axioms PM.RamifiedSyntax.star_2_52
#print axioms PM.RamifiedSyntax.star_2_521
#print axioms PM.RamifiedSyntax.star_2_53
#print axioms PM.RamifiedSyntax.star_2_54
#print axioms PM.RamifiedSyntax.star_2_55
#print axioms PM.RamifiedSyntax.star_2_56
#print axioms PM.RamifiedSyntax.star_2_6
#print axioms PM.RamifiedSyntax.star_2_61
#print axioms PM.RamifiedSyntax.star_2_62
#print axioms PM.RamifiedSyntax.star_2_621
#print axioms PM.RamifiedSyntax.star_2_65
#print axioms PM.RamifiedSyntax.star_2_67
#print axioms PM.RamifiedSyntax.star_2_68
#print axioms PM.RamifiedSyntax.star_2_69
