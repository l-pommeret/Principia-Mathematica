import Principia.Deduction.Star40Derived
import Principia.Deduction.Star41Derived
import Principia.FirstEdition.Volume1.Star42Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱42 — iterated products and sums

The nine propositions of ✱42 compare a sum (or product) taken over an *image*
with the same operation taken over a *sum*.  Both members are memberships, and
both are obtained from the matrices printed at ✱40·01 and ✱40·02 — read, as
PM's typical ambiguity requires, at whatever sort the members happen to have.
Those two matrices are supplied below as eliminable definitions with their
`rfl` unfoldings, so that the two members of each printed equality are built
independently and can be compared constructor by constructor.

No class term, no image term and no sum term is introduced: `pʻκ`, `sʻκ` and
`sʻʻκ` remain incomplete symbols.
-/

/-! ## The two ✱40 matrices at an arbitrary member sort -/

/-- The matrix printed at ✱40·02, `(∃α). α ∈ κ . x ∈ α`, with the member sort
and the two ramified orders left independent.

The bound member is the apparent variable of index zero in both conjuncts:
`collectionMembership` is `α ∈ κ` and `elementMembership` is `x ∈ α`. -/
def star_42_sumMatrix
    (existential : ExistentialVocabulary signature memberSort
      (max collectionOrder elementOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (elementNegation : signature.Negation elementOrder)
    (outerNegation : signature.Negation (max collectionOrder elementOrder))
    (disjunction : signature.Disjunction (max collectionOrder elementOrder))
    (collectionMembership :
      Formula signature real (memberSort :: apparent) collectionOrder)
    (elementMembership :
      Formula signature real (memberSort :: apparent) elementOrder) :
    Formula signature real apparent
      (bindOrder (max collectionOrder elementOrder) memberSort) :=
  .sometimes existential
    (mixedConjunction collectionNegation elementNegation outerNegation
      disjunction collectionMembership elementMembership)

theorem star_42_sumMatrix_unfold
    (existential : ExistentialVocabulary signature memberSort
      (max collectionOrder elementOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (elementNegation : signature.Negation elementOrder)
    (outerNegation : signature.Negation (max collectionOrder elementOrder))
    (disjunction : signature.Disjunction (max collectionOrder elementOrder))
    (collectionMembership :
      Formula signature real (memberSort :: apparent) collectionOrder)
    (elementMembership :
      Formula signature real (memberSort :: apparent) elementOrder) :
    star_42_sumMatrix existential collectionNegation elementNegation
        outerNegation disjunction collectionMembership elementMembership =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation
            (.neg outerNegation
              (.disj disjunction
                (.neg collectionNegation collectionMembership)
                (.neg elementNegation elementMembership))))) := rfl

/-- The matrix printed at ✱40·01, `α ∈ κ .⊃ₐ. x ∈ α`, with the member sort
and the two ramified orders left independent. -/
def star_42_productMatrix
    (universal : signature.Universal memberSort
      (max collectionOrder elementOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (disjunction : signature.Disjunction (max collectionOrder elementOrder))
    (collectionMembership :
      Formula signature real (memberSort :: apparent) collectionOrder)
    (elementMembership :
      Formula signature real (memberSort :: apparent) elementOrder) :
    Formula signature real apparent
      (bindOrder (max collectionOrder elementOrder) memberSort) :=
  .always universal
    (mixedImplication collectionNegation disjunction collectionMembership
      elementMembership)

theorem star_42_productMatrix_unfold
    (universal : signature.Universal memberSort
      (max collectionOrder elementOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (disjunction : signature.Disjunction (max collectionOrder elementOrder))
    (collectionMembership :
      Formula signature real (memberSort :: apparent) collectionOrder)
    (elementMembership :
      Formula signature real (memberSort :: apparent) elementOrder) :
    star_42_productMatrix universal collectionNegation disjunction
        collectionMembership elementMembership =
      .always universal
        (.disj disjunction (.neg collectionNegation collectionMembership)
          elementMembership) := rfl

/-! ## ✱42·1, the two members built apart

PM's chain for `sʻsʻʻκ = sʻsʻκ` runs

```
x ∈ sʻsʻʻκ . ≡ : (∃β). β ∈ sʻʻκ . x ∈ β        [✱40·11]
             ≡ : (∃β,μ). μ ∈ κ . β = sʻμ . x ∈ β   [✱37·1]
             ≡ : (∃μ). μ ∈ κ . x ∈ sʻμ            [✱13·195]
             ≡ : (∃μ,α). μ ∈ κ . α ∈ μ . x ∈ α    [✱40·11]
             ≡ : (∃α). α ∈ sʻκ . x ∈ α            [✱40·11]
             ≡ : x ∈ sʻsʻκ                        [✱40·11]
```

The two members recorded below are the second and the fifth line, each in the
nested form its own operator produces.  They differ in exactly one leaf: the
left carries the image equation `β = sʻμ` of ✱37·01, the right the membership
`α ∈ μ` of ✱40·02.
-/

/-- The left member of ✱42·1: `x ∈ sʻsʻʻκ`, the sum over the image `sʻʻκ`. -/
def star_42_1_left
    (outerExistential : ExistentialVocabulary signature memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (imageNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (elementNegation : signature.Negation elementOrder)
    (outerOuterNegation : signature.Negation
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (imageEquation :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort) :=
  star_42_sumMatrix outerExistential imageNegation elementNegation
    outerOuterNegation outerDisjunction
    (star_42_sumMatrix innerExistential collectionNegation memberNegation
      innerOuterNegation innerDisjunction kappaMembership imageEquation)
    elementMembership

/-- The right member of ✱42·1: `x ∈ sʻsʻκ`, the sum over the sum `sʻκ`. -/
def star_42_1_right
    (outerExistential : ExistentialVocabulary signature memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (sumNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (elementNegation : signature.Negation elementOrder)
    (outerOuterNegation : signature.Negation
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (memberMembership :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort) :=
  star_42_sumMatrix outerExistential sumNegation elementNegation
    outerOuterNegation outerDisjunction
    (star_42_sumMatrix innerExistential collectionNegation memberNegation
      innerOuterNegation innerDisjunction kappaMembership memberMembership)
    elementMembership

/-- Audited reading of ✱42·1. -/
def star_42_1_reading
    (outerExistential : ExistentialVocabulary signature memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (imageNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (elementNegation : signature.Negation elementOrder)
    (outerOuterNegation : signature.Negation
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (equalityNegation : signature.Negation
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort))
    (equalityDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (imageEquation memberMembership :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱42·1. ⊢ . sʻsʻʻκ = sʻsʻκ"
  scopeReading :=
    "Both sums are eliminated by ✱40·02; the printed equality of classes is the ✱20·43 equivalence of the two memberships, and the left member additionally carries the ✱37·01 image equation."
  parsed := .assertion (star_4_01 equalityNegation equalityDisjunction
    (star_42_1_left outerExistential innerExistential collectionNegation
      memberNegation innerOuterNegation innerDisjunction imageNegation
      elementNegation outerOuterNegation outerDisjunction kappaMembership
      imageEquation elementMembership)
    (star_42_1_right outerExistential innerExistential collectionNegation
      memberNegation innerOuterNegation innerDisjunction imageNegation
      elementNegation outerOuterNegation outerDisjunction kappaMembership
      memberMembership elementMembership))

/-! ## ✱42·11, the two members built apart -/

/-- The left member of ✱42·11: `x ∈ pʻpʻʻκ`, the product over the image
`pʻʻκ`. -/
def star_42_11_left
    (outerUniversal : signature.Universal memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (imageNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (imageEquation :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort) :=
  star_42_productMatrix outerUniversal imageNegation outerDisjunction
    (star_42_sumMatrix innerExistential collectionNegation memberNegation
      innerOuterNegation innerDisjunction kappaMembership imageEquation)
    elementMembership

/-- The right member of ✱42·11: `x ∈ pʻsʻκ`, the product over the sum
`sʻκ`. -/
def star_42_11_right
    (outerUniversal : signature.Universal memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (sumNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (memberMembership :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort) :=
  star_42_productMatrix outerUniversal sumNegation outerDisjunction
    (star_42_sumMatrix innerExistential collectionNegation memberNegation
      innerOuterNegation innerDisjunction kappaMembership memberMembership)
    elementMembership

/-- Audited reading of ✱42·11. -/
def star_42_11_reading
    (outerUniversal : signature.Universal memberSort
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (innerExistential : ExistentialVocabulary signature collectionSort
      (max collectionOrder memberOrder))
    (collectionNegation : signature.Negation collectionOrder)
    (memberNegation : signature.Negation memberOrder)
    (innerOuterNegation : signature.Negation (max collectionOrder memberOrder))
    (innerDisjunction : signature.Disjunction (max collectionOrder memberOrder))
    (imageNegation : signature.Negation
      (bindOrder (max collectionOrder memberOrder) collectionSort))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (max collectionOrder memberOrder) collectionSort)
        elementOrder))
    (equalityNegation : signature.Negation
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort))
    (equalityDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (max collectionOrder memberOrder) collectionSort)
          elementOrder)
        memberSort))
    (kappaMembership :
      Formula signature real [collectionSort, memberSort] collectionOrder)
    (imageEquation memberMembership :
      Formula signature real [collectionSort, memberSort] memberOrder)
    (elementMembership : Formula signature real [memberSort] elementOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱42·11. ⊢ . pʻpʻʻκ = pʻsʻκ"
  scopeReading :=
    "The outer product is eliminated by ✱40·01 and the inner collection by ✱40·02; the left member additionally carries the ✱37·01 image equation."
  parsed := .assertion (star_4_01 equalityNegation equalityDisjunction
    (star_42_11_left outerUniversal innerExistential collectionNegation
      memberNegation innerOuterNegation innerDisjunction imageNegation
      outerDisjunction kappaMembership imageEquation elementMembership)
    (star_42_11_right outerUniversal innerExistential collectionNegation
      memberNegation innerOuterNegation innerDisjunction imageNegation
      outerDisjunction kappaMembership memberMembership elementMembership))

/-!
## What still resists, at the level of `Formula` constructors

For ✱42·1 the two recorded members are

```
left  = .neg out (.always uni (.neg mat (.neg o (.disj d (.neg n INNER_IMAGE) (.neg e ELEM)))))
right = .neg out (.always uni (.neg mat (.neg o (.disj d (.neg n INNER_SUM)   (.neg e ELEM)))))
```

and `INNER_IMAGE`, `INNER_SUM` agree down to their last conjunct, where one
holds `imageEquation` (`β = sʻμ`) and the other `memberMembership` (`α ∈ μ`).
The two trees are therefore *not* convertible, and they must not be: PM's own
demonstration needs three further propositions to identify them —

* ✱37·1, to turn `β ∈ sʻʻκ` into `(∃μ). μ ∈ κ . β = sʻμ`;
* ✱13·195, to eliminate the image equation `β = sʻμ` under the existential;
* ✱11·55, to reassociate `(∃β,μ)` into `(∃μ,β)` before ✱40·11 is applied the
  second time.

✱13·195 is not yet derived here, and ✱40·11 itself still carries the
reducibility-scope transport premise of ✱20·3.  Asserting ✱42·1 would
therefore mean either identifying `imageEquation` with `memberMembership` —
which is exactly the collapse the two-sided gate exists to catch — or
inventing a class term for `sʻμ`.  Neither is done.

The same diagnosis applies verbatim to ✱42·11, and, after replacing
`memberSort` by `relationSort` and ✱40·01·02 by ✱41·01·02, to ✱42·12 and
✱42·13.

✱42·2, ✱42·21 and ✱42·22 print chains of four, five and eight members built
from `Cʻ`, `Fʻʻ` and `F⃗ⁿ`.  Each member is a distinct class-valued incomplete
symbol; a Lean equality between them can only be had by defining them all as
one term, which is what the previous `Architecture` reconstruction did and
what the catalogue records as
`blocked-semantic-mismatch-definitional-alias-collapse`.  ✱42·3 and ✱42·31
need in addition the image of a plural descriptive function (✱37·01 applied to
`R⃗`), and rest on ✱40·5, itself downstream of ✱40·11.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_42_sumMatrix_unfold
#print axioms PM.RamifiedSyntax.star_42_productMatrix_unfold
