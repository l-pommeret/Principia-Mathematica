import Principia.Deduction.Star33Derived
import Principia.FirstEdition.Volume1.Star51Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Definitions and derived propositions of PM I, ✱51

The relation `ι` of ✱51·01 has a class as its left argument and an individual
as its right argument. It is therefore the heterogeneous instance of the
contextual relation abstraction exposed by `binaryAbstraction`; it is not a
new relation-valued term.

No proposition of ✱51 is declared here.  The former relation-elimination
obstruction is no longer current: `binaryElimination` now supplies the
heterogeneous systematic-ambiguity instance needed for a relation between a
class and an individual, and ✱50·1 is available in `Star50Derived`.

What blocks ✱51·1 is one level lower, and it is a *representation* fact, not
a missing derivation.  ✱51·01 reads `ι = I⃗`, so the matrix of ✱51·01 is the
sectional function of ✱32·01 applied to the relation `I` of ✱50·01.  ✱32·01 is
`R⃗ = α̂ŷ{α = x̂(xRy)}`, and its reconstruction — like every relation operator
of ✱31 to ✱37 — takes `R` as a `Term` of relation sort.  `I` is not a term:
✱50·01 is a `Df`, so `I` is an incomplete symbol and `star_50_relationApplication`
is a `Formula` rooted at `Formula.neg`.  `star_51_class_terms_are_atomic`
below records the same fact at the class sort.  Hence `I⃗` has no AST, and the
`identityImageMatrix` parameter of `star_51_01` is left open on purpose: it
marks the exact place where the printed definition cannot yet be closed.

What *is* exact is the other member.  `star_51_unitClass` below builds
`ŷ(y = x)` from ✱20·01 at PM's own ✱13·01 matrix, and
`star_51_unitClassIdentity` builds the printed `α = ŷ(y = x)`, which is the
right member of ✱51·1 and of ✱51·13 and the subject of everything from ✱51·2
to ✱51·4.

✱51·11 additionally waits for the descriptive-function equality ✱30·3.  The
later propositions consume these openings (although ✱14·21 itself is now
available).  Thus the honest total remains zero without assuming an asserted
target or changing the printed dependency path.
-/

/-- Logical vocabulary for the heterogeneous contextual definition ✱51·01. -/
structure Star51DefinitionVocabulary (signature : Signature)
    (classOrder relationOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [classSort classOrder 0, .individual] relationOrder 0)
    (max
      (bindOrder (bindOrder relationOrder (classSort classOrder 0)) .individual)
      scopeOrder)
  classUniversal : signature.Universal (classSort classOrder 0) relationOrder
  individualUniversal : signature.Universal .individual
    (bindOrder relationOrder (classSort classOrder 0))
  equivalenceNegation : signature.Negation relationOrder
  equivalenceDisjunction : signature.Disjunction relationOrder
  leftNegation : signature.Negation
    (bindOrder (bindOrder relationOrder (classSort classOrder 0)) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder (bindOrder relationOrder (classSort classOrder 0)) .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder relationOrder (classSort classOrder 0)) .individual)
      scopeOrder)

/-- ✱51·01, `ι = I⃗`: the defined relation is the contextual abstraction of
the displayed `α I⃗ x` matrix. The matrix is supplied at its exact ramified
order because the earlier sectional operator `I⃗` is itself incomplete. -/
def star_51_01
    (vocabulary : Star51DefinitionVocabulary signature classOrder
      relationOrder scopeOrder)
    (identityImageMatrix : Formula signature real
      (classSort classOrder 0 :: .individual :: apparent) relationOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0, .individual] relationOrder 0 ::
        apparent) scopeOrder) :=
  binaryAbstraction vocabulary.existential vocabulary.classUniversal
    vocabulary.individualUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction identityImageMatrix continuation

/-- The complete heterogeneous relation-abstraction expansion of ✱51·01. -/
theorem star_51_01_unfold
    (vocabulary : Star51DefinitionVocabulary signature classOrder
      relationOrder scopeOrder)
    (identityImageMatrix : Formula signature real
      (classSort classOrder 0 :: .individual :: apparent) relationOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0, .individual] relationOrder 0 ::
        apparent) scopeOrder) :
    star_51_01 vocabulary identityImageMatrix continuation =
      binaryAbstraction vocabulary.existential vocabulary.classUniversal
        vocabulary.individualUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction identityImageMatrix continuation := rfl

/-- Audited definitional reading of the PM-VERBATIM block ✱51·01. -/
def star_51_01_reading
    (vocabulary : Star51DefinitionVocabulary signature classOrder
      relationOrder scopeOrder)
    (identityImageMatrix : Formula signature real
      [classSort classOrder 0, .individual] relationOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0, .individual] relationOrder 0]
      scopeOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱51·01. ι = I⃗  Df"
  parsed := .assertion
    (star_51_01 vocabulary identityImageMatrix continuation)
  scopeReading :=
    "The defined heterogeneous relation has the scope supplied by the continuation; I⃗ remains contextual."

/-! ## The unit class `ŷ(y = x)`

Every printed proposition from ✱51·1 to ✱51·4 is about this one class.  It is
an incomplete symbol: ✱20·01 expands it contextually, and no class-valued
`Term` appears.  The construction below is exact — the matrix is PM's own
✱13·01 — so the obstruction diagnosed at the end of the module is about
*derivation*, not about representation. -/

/-- The order of the ✱13·01 identity that ✱51 uses at individual arguments. -/
def star_51_identityOrder (identityOrder identityExcess : Nat) : Nat :=
  bindOrder identityOrder (.function [.individual] identityOrder identityExcess)

/-- The matrix of `ŷ(y = x)`.  Under the ✱20·01 binder the head apparent
variable is the abstraction variable `y`; the displayed argument `x` is pushed
across it. -/
def star_51_unitClassMatrix
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual) :
    Formula signature real (.individual :: apparent)
      (star_51_identityOrder identityOrder identityExcess) :=
  star_13_01 identity (.apparent .zero) x.weaken

theorem star_51_unitClassMatrix_unfold
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual) :
    star_51_unitClassMatrix identity x =
      star_13_01 identity (.apparent .zero) x.weaken := rfl

/-- The ✱20·01 vocabulary the unit class needs at the order its ✱13·01 matrix
carries. -/
structure Star51UnitClassVocabulary (signature : Signature)
    (identityOrder identityExcess scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (classSort (star_51_identityOrder identityOrder identityExcess) 0)
    (max
      (bindOrder (star_51_identityOrder identityOrder identityExcess)
        .individual)
      scopeOrder)
  universal : signature.Universal .individual
    (star_51_identityOrder identityOrder identityExcess)
  equivalenceNegation : signature.Negation
    (star_51_identityOrder identityOrder identityExcess)
  equivalenceDisjunction : signature.Disjunction
    (star_51_identityOrder identityOrder identityExcess)
  leftNegation : signature.Negation
    (bindOrder (star_51_identityOrder identityOrder identityExcess) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder (star_51_identityOrder identityOrder identityExcess)
        .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder (star_51_identityOrder identityOrder identityExcess)
        .individual)
      scopeOrder)

/-- `ŷ(y = x)`: the contextual class abstraction of ✱20·01 at the identity
matrix.  The continuation carries the scope PM gives the incomplete symbol. -/
def star_51_unitClass
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual)
    (continuation : Formula signature real
      (classSort (star_51_identityOrder identityOrder identityExcess) 0 ::
        apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max
          (bindOrder (star_51_identityOrder identityOrder identityExcess)
            .individual)
          scopeOrder)
        (classSort (star_51_identityOrder identityOrder identityExcess) 0)) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_51_unitClassMatrix identity x) continuation

theorem star_51_unitClass_unfold
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual)
    (continuation : Formula signature real
      (classSort (star_51_identityOrder identityOrder identityExcess) 0 ::
        apparent) scopeOrder) :
    star_51_unitClass vocabulary identity x continuation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_51_unitClassMatrix identity x) continuation := rfl

/-- `α = ŷ(y = x)`, the right member printed at ✱51·1 and at ✱51·13.  The
class abstraction keeps the ✱13·01 identity as its scope, so the two printed
`=` signs are the individual-sort and class-sort instances of one definition
and no class-valued term is created. -/
def star_51_unitClassIdentity
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess
      (bindOrder classOrder
        (.function
          [classSort (star_51_identityOrder identityOrder identityExcess) 0]
          classOrder classExcess)))
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (classIdentity : IdentityVocabulary signature
      (classSort (star_51_identityOrder identityOrder identityExcess) 0)
      classOrder classExcess)
    (alpha : Term signature real apparent
      (classSort (star_51_identityOrder identityOrder identityExcess) 0))
    (x : Term signature real apparent .individual) :=
  star_51_unitClass vocabulary identity x
    (star_13_01 classIdentity alpha.weaken (.apparent .zero))

theorem star_51_unitClassIdentity_unfold
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess
      (bindOrder classOrder
        (.function
          [classSort (star_51_identityOrder identityOrder identityExcess) 0]
          classOrder classExcess)))
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (classIdentity : IdentityVocabulary signature
      (classSort (star_51_identityOrder identityOrder identityExcess) 0)
      classOrder classExcess)
    (alpha : Term signature real apparent
      (classSort (star_51_identityOrder identityOrder identityExcess) 0))
    (x : Term signature real apparent .individual) :
    star_51_unitClassIdentity vocabulary identity classIdentity alpha x =
      star_51_unitClass vocabulary identity x
        (star_13_01 classIdentity alpha.weaken (.apparent .zero)) := rfl

/-! ### Why ✱51·1--✱51·4 do not close -/

/-- The seven roots of `Formula`, used to compare the trees below. -/
private inductive Star51Root where
  | proposition
  | apply
  | neg
  | disj
  | always
  | incompleteScope
  | descriptionScope

private def star51Root :
    Formula signature real apparent order → Star51Root
  | .proposition _ => .proposition
  | .apply _ _ => .apply
  | .neg _ _ => .neg
  | .disj _ _ _ => .disj
  | .always _ _ => .always
  | .incompleteScope _ _ _ _ _ _ _ => .incompleteScope
  | .descriptionScope _ _ _ _ _ => .descriptionScope

/-- Every term of class sort is a variable or a signature symbol: `Term` has
no abstraction constructor.  Inclusion ✱22·01, intersection ✱22·02, union
✱22·03 and difference ✱22·03 are all declared with class `Term` arguments, so
the printed subjects `ιʻx ⊂ α`, `α ∩ ιʻx`, `α − ιʻx` of ✱51·2 to ✱51·4 have no
AST here. -/
theorem star_51_class_terms_are_atomic
    (classTerm : Term signature real apparent (classSort resultOrder classExcess)) :
    (∃ v : Var real (classSort resultOrder classExcess),
        classTerm = .real v) ∨
      (∃ v : Var apparent (classSort resultOrder classExcess),
        classTerm = .apparent v) ∨
      (∃ s : signature.Symbol (classSort resultOrder classExcess),
        classTerm = .symbol s) := by
  cases classTerm with
  | real v => exact Or.inl ⟨v, rfl⟩
  | apparent v => exact Or.inr (Or.inl ⟨v, rfl⟩)
  | symbol payload => exact Or.inr (Or.inr ⟨payload, rfl⟩)

/-- `ŷ(y = x)` is rooted at `Formula.neg`, because ✱10·01 turns the ✱20·01
existential into `∼(φ).∼…`.  Membership ✱20·02 is `Formula.apply`; the two
trees differ at the root constructor. -/
theorem star_51_unitClass_root
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual)
    (continuation : Formula signature real
      (classSort (star_51_identityOrder identityOrder identityExcess) 0 ::
        apparent) scopeOrder) :
    star51Root (star_51_unitClass vocabulary identity x continuation) = .neg :=
  rfl

/-- The membership formula the printed `y ε ιʻx` needs is an application of a
class term; `star_51_unitClass` is not one. -/
theorem star_51_unitClass_ne_membership
    (vocabulary : Star51UnitClassVocabulary signature identityOrder
      identityExcess scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (x : Term signature real apparent .individual)
    (continuation : Formula signature real
      (classSort (star_51_identityOrder identityOrder identityExcess) 0 ::
        apparent) scopeOrder)
    (classTerm : Term signature real apparent
      (classSort
        (bindOrder
          (max
            (bindOrder (star_51_identityOrder identityOrder identityExcess)
              .individual)
            scopeOrder)
          (classSort (star_51_identityOrder identityOrder identityExcess) 0))
        0))
    (y : Term signature real apparent .individual) :
    star_51_unitClass vocabulary identity x continuation ≠
      membership y classTerm := by
  intro equality
  have rootEquality := congrArg star51Root equality
  cases rootEquality

/-!
## Exact stopping point for ✱51·1--✱51·4

The representation is now complete on one side and provably impossible on the
other, and neither side is a matter of taste.

*✱51·1.*  Its right member is `star_51_unitClassIdentity`, exact.  Its left
member `α ι x` is `star_51_01`, whose matrix is the sectional `α I⃗ x`, and the
printed demonstration reaches it in three steps: `✱4·2.(✱51·01)`, then
`[✱32·1]`, then `[✱50·1]`.  The middle step is now available as a conditional
theorem, but only for a relation supplied as a `Term`; `I` is an incomplete
symbol, so `I⃗` cannot be formed and `star_51_01` keeps its matrix open.  The
first step, moreover, would fold the two members of an equivalence onto the
same expression, which is exactly the collapse `verify_two_sided_readings`
exists to reject.  So ✱51·1 is not asserted here, in either direction.

*✱51·11--✱51·17.*  `ιʻx` is a descriptive function, so it needs ✱30·01 with
✱30·3; `Star30Derived` stops at ✱30·2.  Everything printed from ✱51·12 to
✱51·17 is stated about `ιʻx`, so all of it waits on the same opening.

*✱51·2--✱51·4.*  Each printed subject — `ιʻx ⊂ α` (✱51·2), `α − ιʻx`
(✱51·21, ✱51·221, ✱51·3), `ιʻx ∩ α` (✱51·211, ✱51·31), `ιʻx ∪ ιʻy` (✱51·232
onwards), `−ιʻx` (✱51·34--✱51·36) — puts the unit class in an argument place
that ✱22·01--✱22·03 reserve for a class `Term`.  By
`star_51_class_terms_are_atomic` such a term is a variable or a symbol, while
`star_51_unitClass` is a `Formula` rooted at `Formula.neg`
(`star_51_unitClass_root`), and `star_51_unitClass_ne_membership` shows it is
not the `Formula.apply` that ✱20·02 membership produces either.  The printed
subjects therefore have no AST, and no equality between trees is statable.

Behind both is one arithmetic fact.  Eliminating a contextual abstraction
needs PM's scope propositions ✱10·27/✱10·28 — here `star_9_21`/`star_9_22` —
and those are reconstructed at matrix order `0` alone, while the ✱13·01 matrix
of the unit class has order `star_51_identityOrder identityOrder
identityExcess`, a `bindOrder` and so never `0`.  That is the same wall
recorded at the end of `Star50Derived`.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_51_01
#print axioms PM.RamifiedSyntax.star_51_01_unfold
#print axioms PM.RamifiedSyntax.star_51_01_reading
#print axioms PM.RamifiedSyntax.star_51_unitClassMatrix_unfold
#print axioms PM.RamifiedSyntax.star_51_unitClass_unfold
#print axioms PM.RamifiedSyntax.star_51_unitClassIdentity_unfold
#print axioms PM.RamifiedSyntax.star_51_class_terms_are_atomic
#print axioms PM.RamifiedSyntax.star_51_unitClass_root
#print axioms PM.RamifiedSyntax.star_51_unitClass_ne_membership
