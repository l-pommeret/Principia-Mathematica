import Principia.Deduction.ScopeBridgeB

/-!
# Closed-member scope transport

This module records the literal, independently built members of PM I,
✱9·03--·06.  They are deliberately not identified by an equality of
`Formula` trees: the external member and the scoped member have different
root constructors.

The missing derivational step is recorded below as
`scope_transport_missing_internal_to_external`.  It is the non-reflexive reading of
✱10·12 required at line (1) of PM's printed proof of ✱10·2.  No
`Derivation` of that reading is declared here.
-/

namespace PM.RamifiedSyntax

structure ScopeTransportReading (signature : Signature) (real : Context) where
  printed : String
  parsed : Claim signature real

/- Assigned-order transport only.  This changes no constructor of the
formula and is used solely to put the two independently built members at the
arithmetically equal order required by `equivalence`. -/
private def Formula.scopeTransportCast
    (formula : Formula signature real apparent sourceOrder) :
    {targetOrder : Nat} → sourceOrder = targetOrder →
      Formula signature real apparent targetOrder
  | _, rfl => formula

/-! ## ✱9·03 -/

/-- Literal external member `(x).φx ∨ p` of ✱9·03. -/
def scope_transport_closed_right_external
    (matrixUniversal : signature.Universal argument matrixOrder)
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (body : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  Formula.scopeTransportCast
    (.disj outerDisjunction (.always matrixUniversal body) fixed)
    (bindOrderMaxRight matrixOrder fixedOrder argument)

/-- The requested judgement-level reading of ✱9·03. -/
def scope_transport_closed_right_reading
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max matrixOrder fixedOrder))
    (scopeDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (resultNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (body : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder) :
    ScopeTransportReading signature real where
  printed := "⊢ : (x).φx .∨. p .≡ : (x).φx ∨ p"
  parsed := .assertion (equivalence resultNegation resultDisjunction
    (scope_transport_closed_right_external matrixUniversal outerDisjunction
      body fixed)
    (star_9_03 scopeUniversal scopeDisjunction body fixed))

/-! ## ✱9·04 and the exact ✱10·12 gap -/

/-- Literal external member `p ∨ (x).φx` of ✱9·04. -/
def scope_transport_closed_left_external
    (matrixUniversal : signature.Universal argument matrixOrder)
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (fixed : Formula signature real [] fixedOrder)
    (body : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  Formula.scopeTransportCast
    (.disj outerDisjunction fixed (.always matrixUniversal body))
    (bindOrderMaxLeft fixedOrder matrixOrder argument)

/-- The requested judgement-level reading of ✱9·04. -/
def scope_transport_closed_left_reading
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (scopeDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (resultNegation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (fixed : Formula signature real [] fixedOrder)
    (body : Formula signature real [argument] matrixOrder) :
    ScopeTransportReading signature real where
  printed := "⊢ : p .∨. (x).φx .≡ : (x).p ∨ φx"
  parsed := .assertion (equivalence resultNegation resultDisjunction
    (scope_transport_closed_left_external matrixUniversal outerDisjunction
      fixed body)
    (star_9_04 scopeUniversal scopeDisjunction fixed body))

/-- The exact non-reflexive ✱10·12 needed in line (1) of PM's proof of
✱10·2:

`⊢ : (x).p ∨ φx .⊃ : p .∨. (x).φx`.

The existing `star_10_12` has the same scoped AST on both sides and therefore
does not inhabit this reading. -/
def scope_transport_missing_internal_to_external
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (scopeDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (resultNegation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (fixed : Formula signature real [] fixedOrder)
    (body : Formula signature real [argument] matrixOrder) :
    ScopeTransportReading signature real where
  printed := "⊢ : (x).p ∨ φx .⊃ : p .∨. (x).φx"
  parsed := .assertion (implication resultNegation resultDisjunction
    (star_9_04 scopeUniversal scopeDisjunction fixed body)
    (scope_transport_closed_left_external matrixUniversal outerDisjunction
      fixed body))

/-! ## ✱9·05 -/

/-- Literal external member `(∃x).φx ∨ p` of ✱9·05. -/
def scope_transport_existential_right_external
    (matrixExistential :
      ExistentialVocabulary signature argument matrixOrder)
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (body : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  Formula.scopeTransportCast
    (.disj outerDisjunction (.sometimes matrixExistential body) fixed)
    (bindOrderMaxRight matrixOrder fixedOrder argument)

/-- The requested judgement-level reading of ✱9·05. -/
def scope_transport_existential_right_reading
    (matrixExistential :
      ExistentialVocabulary signature argument matrixOrder)
    (scopeExistential : ExistentialVocabulary signature argument
      (max matrixOrder fixedOrder))
    (scopeDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (resultNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (body : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder) :
    ScopeTransportReading signature real where
  printed := "⊢ : (∃x).φx .∨. p .≡ : (∃x).φx ∨ p"
  parsed := .assertion (equivalence resultNegation resultDisjunction
    (scope_transport_existential_right_external matrixExistential outerDisjunction
      body fixed)
    (star_9_05 scopeExistential scopeDisjunction body fixed))

/-! ## ✱9·06 -/

/-- Literal external member `p ∨ (∃x).φx` of ✱9·06. -/
def scope_transport_existential_left_external
    (matrixExistential :
      ExistentialVocabulary signature argument matrixOrder)
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (fixed : Formula signature real [] fixedOrder)
    (body : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  Formula.scopeTransportCast
    (.disj outerDisjunction fixed (.sometimes matrixExistential body))
    (bindOrderMaxLeft fixedOrder matrixOrder argument)

/-- The requested judgement-level reading of ✱9·06. -/
def scope_transport_existential_left_reading
    (matrixExistential :
      ExistentialVocabulary signature argument matrixOrder)
    (scopeExistential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (scopeDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (resultNegation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (fixed : Formula signature real [] fixedOrder)
    (body : Formula signature real [argument] matrixOrder) :
    ScopeTransportReading signature real where
  printed := "⊢ : p .∨. (∃x).φx .≡ : (∃x).p ∨ φx"
  parsed := .assertion (equivalence resultNegation resultDisjunction
    (scope_transport_existential_left_external matrixExistential outerDisjunction
      fixed body)
    (star_9_06 scopeExistential scopeDisjunction fixed body))

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.scope_transport_closed_right_reading
#print axioms PM.RamifiedSyntax.scope_transport_closed_left_reading
#print axioms PM.RamifiedSyntax.scope_transport_missing_internal_to_external
#print axioms PM.RamifiedSyntax.scope_transport_existential_right_reading
#print axioms PM.RamifiedSyntax.scope_transport_existential_left_reading
