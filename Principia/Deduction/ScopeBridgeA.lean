import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-- The right member proposed for `scope_neg_always` unfolds to two matrix
negations, not to the matrix `body` occurring on the proposed left member. -/
theorem scope_neg_always_rhs_normal_form
    {signature : Signature} {real apparent : Context}
    {argument : RSort} {matrixOrder : Nat}
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula.sometimes existential
        (Formula.neg existential.matrixNegation body) =
      Formula.neg existential.outerNegation
        (Formula.always existential.universal
          (Formula.neg existential.matrixNegation
            (Formula.neg existential.matrixNegation body))) := by
  rfl

/-- The left member proposed for `scope_neg_sometimes` retains two outer
`neg` constructors when `sometimes` is unfolded. -/
theorem scope_neg_sometimes_lhs_normal_form
    {signature : Signature} {real apparent : Context}
    {argument : RSort} {matrixOrder : Nat}
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula.neg existential.outerNegation
        (Formula.sometimes existential body) =
      Formula.neg existential.outerNegation
        (Formula.neg existential.outerNegation
          (Formula.always existential.universal
            (Formula.neg existential.matrixNegation body))) := by
  rfl

/-- Consequently the proposed `scope_neg_sometimes` equality identifies a
`neg` root with an `always` root and is rejected by constructor disjointness. -/
theorem scope_neg_sometimes_constructor_mismatch
    {signature : Signature} {real apparent : Context}
    {argument : RSort} {matrixOrder : Nat}
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula.neg existential.outerNegation
        (Formula.sometimes existential body) ≠
      Formula.always existential.universal
        (Formula.neg existential.matrixNegation body) := by
  intro equality
  cases equality

/-- Even when all order indices reduce definitionally, the two proposed
`scope_disj_always` trees have different root constructors.  The fully general
surface equation additionally needs distinct meanings and an order cast. -/
theorem scope_disj_always_constructor_mismatch
    {signature : Signature} {real apparent : Context}
    (universal : signature.Universal .individual 1)
    (disjunction : signature.Disjunction 1)
    (body : Formula signature real (.individual :: apparent) 1)
    (fixed : Formula signature real apparent 0) :
    Formula.disj disjunction (Formula.always universal body) fixed ≠
      Formula.always universal
        (Formula.disj disjunction body (fixed.rename (fun v => .succ v))) := by
  intro equality
  cases equality

end PM.RamifiedSyntax
