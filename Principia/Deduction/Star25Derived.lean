import Principia.Deduction.Star21Derived
import Principia.Deduction.Star22Derived
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star11Derived
import Principia.FirstEdition.Volume1.Star25Source

namespace PM.RamifiedSyntax

/-!
# PM I, ✱25 — universal, null, and existing relations

The relation-forming signs remain contextual incomplete symbols.  The three
definitions below therefore expand through ✱21·01/·02 and never manufacture a
relation-valued term.  PM explicitly says that the unprinted proofs in this
chapter proceed as the corresponding ✱24 proofs.
-/

/-- Vocabulary for one predicative binary relation abstraction ✱21·01. -/
structure Star25RelationVocabulary (signature : Signature)
    (order scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (relationSort order 0)
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
  leftUniversal : signature.Universal .individual order
  rightUniversal : signature.Universal .individual
    (bindOrder order .individual)
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation
    (bindOrder (bindOrder order .individual) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)

/-- The matrix `x = x . y = y` printed in ✱25·01. -/
def star_25_universalMatrix
    (identity : IdentityVocabulary signature .individual identityOrder excess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess))) :
    Formula signature real [.individual, .individual]
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)) :=
  .neg negation (sameDisjunction disjunction
    (.neg negation
      (star_13_01 (realCtx := real)
        (apparent := [.individual, .individual]) identity
        (.apparent .zero) (.apparent .zero)))
    (.neg negation
      (star_13_01 (realCtx := real)
        (apparent := [.individual, .individual]) identity
        (.apparent (.succ .zero)) (.apparent (.succ .zero)))))

/-- ✱25·01, the universal relation as the contextual abstraction
`x̂ŷ(x = x . y = y)`. -/
def star_25_01
    (vocabulary : Star25RelationVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder excess)
    (continuation : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder excess)) 0]
      scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_25_universalMatrix identity vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction)
    continuation

theorem star_25_01_unfold
    (vocabulary : Star25RelationVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder excess)
    (continuation : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder excess)) 0]
      scopeOrder) :
    star_25_01 vocabulary identity continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_25_universalMatrix identity vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction)
        continuation := rfl

/-- ✱25·02, the null relation: complement is eliminated into the negated
matrix of the contextual abstraction. -/
def star_25_02
    (vocabulary : Star25RelationVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder excess)
    (continuation : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder excess)) 0]
      scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg vocabulary.equivalenceNegation
      (star_25_universalMatrix identity vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction))
    continuation

theorem star_25_02_unfold
    (vocabulary : Star25RelationVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder excess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder excess)
    (continuation : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder excess)) 0]
      scopeOrder) :
    star_25_02 vocabulary identity continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (.neg vocabulary.equivalenceNegation
          (star_25_universalMatrix identity vocabulary.equivalenceNegation
            vocabulary.equivalenceDisjunction))
        continuation := rfl

/-- ✱25·03, relation existence as `(∃x,y).xRy`. -/
def star_25_03
    (innerExistential : ExistentialVocabulary signature .individual order)
    (outerExistential : ExistentialVocabulary signature .individual
      (bindOrder order .individual))
    (relation : Term signature real [] (relationSort order 0)) :
    Formula signature real []
      (bindOrder (bindOrder order .individual) .individual) :=
  .sometimes outerExistential
    (.sometimes innerExistential
      (star_21_02 relation.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))))

theorem star_25_03_unfold
    (innerExistential : ExistentialVocabulary signature .individual order)
    (outerExistential : ExistentialVocabulary signature .individual
      (bindOrder order .individual))
    (relation : Term signature real [] (relationSort order 0)) :
    star_25_03 innerExistential outerExistential relation =
      .sometimes outerExistential
        (.sometimes innerExistential
          (star_21_02 relation.weaken.weaken (.apparent .zero)
            (.apparent (.succ .zero)))) := rfl

/-- Audited reading of ✱25·5 after eliminating ✱25·03. -/
def star_25_5_reading
    (innerExistential : ExistentialVocabulary signature .individual order)
    (outerExistential : ExistentialVocabulary signature .individual
      (bindOrder order .individual))
    (relation : Term signature real [] (relationSort order 0))
    (negation : signature.Negation
      (bindOrder (bindOrder order .individual) .individual))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder order .individual) .individual)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱25·5. ⊢:∃̇!R.≡.(∃ x,y).xRy"
  parsed := .assertion (star_4_01 negation disjunction
    (star_25_03 innerExistential outerExistential relation)
    (.sometimes outerExistential
      (.sometimes innerExistential
        (star_21_02 relation.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero))))))
  scopeReading := "The defined left member unfolds by ✱25·03 to the independently constructed double existential on the right."

/-- ✱25·5, the direct unfolding of ✱25·03 followed by ✱4·2.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_25_5
    (innerExistential : ExistentialVocabulary signature .individual order)
    (outerExistential : ExistentialVocabulary signature .individual
      (bindOrder order .individual))
    (relation : Term signature real [] (relationSort order 0))
    (negation : signature.Negation
      (bindOrder (bindOrder order .individual) .individual))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder order .individual) .individual)) :
    Derivation (star_25_5_reading innerExistential outerExistential relation
      negation disjunction).parsed := by
  have line1 := star_25_03_unfold innerExistential outerExistential relation
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_25_03 innerExistential outerExistential relation)
    (.sometimes outerExistential
      (.sometimes innerExistential
        (star_21_02 relation.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero)))))))
  rw [line1]
  have line2 := star_4_2 negation disjunction
    (.sometimes outerExistential
      (.sometimes innerExistential
        (star_21_02 relation.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero)))))
  exact line2

/-- The `xRy` matrix printed on the left of ✱25·58. -/
def star_25_58_leftMatrix
    (relation : Term signature real []
      (relationSort (bindOrder baseOrder .individual) 0)) :
    Formula signature real [.individual, .individual]
      (bindOrder baseOrder .individual) :=
  star_21_02 relation.weaken.weaken (.apparent .zero)
    (.apparent (.succ .zero))

/-- The independently constructed `xSy` matrix printed on the right of
✱25·58. -/
def star_25_58_rightMatrix
    (relation : Term signature real []
      (relationSort (bindOrder baseOrder .individual) 0)) :
    Formula signature real [.individual, .individual]
      (bindOrder baseOrder .individual) :=
  star_21_02 relation.weaken.weaken (.apparent .zero)
    (.apparent (.succ .zero))

/-- Audited scope reading of ✱25·58. -/
def star_25_58_reading
    (inner : signature.Universal .individual
      (bindOrder baseOrder .individual))
    (outer : signature.Universal .individual
      (bindOrder (bindOrder baseOrder .individual) .individual))
    (negation : signature.Negation (bindOrder baseOrder .individual))
    (disjunction : signature.Disjunction (bindOrder baseOrder .individual))
    (relation₁ relation₂ : Term signature real []
      (relationSort (bindOrder baseOrder .individual) 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱25·58. ⊢:. R⪽S.⊃:∃̇!R.⊃.∃̇!S"
  parsed := (star_11_34_reading inner outer negation disjunction
    (star_25_58_leftMatrix relation₁)
    (star_25_58_rightMatrix relation₂)).parsed
  scopeReading := "The binary inclusion and both relation-existence members are the corresponding two-variable scopes of ✱11·34."

/-- ✱25·58, the binary analogue of ✱24·58, obtained from the printed
✱11·34 route (✱10·27·28) for the independently constructed relation matrices.
`demonstration_provenance: editorial-reconstruction-following-✱24`. -/
theorem star_25_58
    (inner : signature.Universal .individual
      (bindOrder baseOrder .individual))
    (outer : signature.Universal .individual
      (bindOrder (bindOrder baseOrder .individual) .individual))
    (negation : signature.Negation (bindOrder baseOrder .individual))
    (disjunction : signature.Disjunction (bindOrder baseOrder .individual))
    (relation₁ relation₂ : Term signature real []
      (relationSort (bindOrder baseOrder .individual) 0)) :
    Derivation (star_25_58_reading inner outer negation disjunction
      relation₁ relation₂).parsed := by
  have line1 := star_11_34 inner outer negation disjunction
    (star_25_58_leftMatrix relation₁)
    (star_25_58_rightMatrix relation₂)
  exact line1

/-!
The other 68 assertions still need the corresponding ramified ✱24 routes.
✱23 now exports the contextual relation operations, and ✱21·3 eliminates them
at displayed arguments modulo its named `reducibility_scope_transport`
premise.  What is not yet exported is the unconditional ✱24 algebra/identity
transport needed to lift those pointwise eliminations through the equalities
printed throughout ✱25.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_25_01_unfold
#print axioms PM.RamifiedSyntax.star_25_02_unfold
#print axioms PM.RamifiedSyntax.star_25_03_unfold
#print axioms PM.RamifiedSyntax.star_25_5
#print axioms PM.RamifiedSyntax.star_25_58
