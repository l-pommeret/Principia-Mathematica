import Principia.FirstEdition.Volume1.Star20Source
import Principia.Syntax.Ramified
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star5Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.Deduction.Star13Derived

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱20 -/

/-! ## The class of classes ✱20·03 -/

/-- ✱20·03: `Cls` is the contextual class abstraction whose displayed
matrix says that its class argument is represented by a predicative unary
function.  The exact inner matrix is supplied as syntax data; the outer
abstraction itself is fully eliminated here. -/
def star_20_03
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (classSort classOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder)
        (.function [classSort classOrder 0] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_20_03_unfold
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (classSort classOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_20_03 existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-- Printed-to-AST reading of ✱20·03. -/
def star_20_03_reading
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real [classSort classOrder 0] resultOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "Cls = ẑ((∃φ). α = ẑ(φ!z))  Df"
  parsed := .assertion
    (star_20_03 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)

/-- ✱20·04: comma-separated double membership is conjunction. -/
def star_20_04
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (left right : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  mixedConjunction negation negation negation disjunction left right

theorem star_20_04_unfold
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (left right : Formula signature real apparent 0) :
    star_20_04 negation disjunction left right =
      mixedConjunction negation negation negation disjunction left right := rfl

/-- ✱20·05: comma-separated triple membership associates to the left, as
shown by PM's defining right-hand side. -/
def star_20_05
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (first second third : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  mixedConjunction negation negation negation disjunction
    (star_20_04 negation disjunction first second) third

theorem star_20_05_unfold
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (first second third : Formula signature real apparent 0) :
    star_20_05 negation disjunction first second third =
      mixedConjunction negation negation negation disjunction
        (star_20_04 negation disjunction first second) third := rfl

/-- ✱20·06: non-membership is the negation of membership. -/
def star_20_06
    (negation : signature.Negation order)
    (membership : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation membership

theorem star_20_06_unfold
    (negation : signature.Negation order)
    (membership : Formula signature real apparent order) :
    star_20_06 negation membership = .neg negation membership := rfl

/-- ✱20·07: quantification over classes is quantification over predicative
one-place functions.  `classSort resultOrder 0` records the essential `!`. -/
def star_20_07
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (classSort resultOrder 0)) :=
  .always universal body

theorem star_20_07_unfold
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    star_20_07 universal body = .always universal body := rfl

/-- ✱20·071: existential class quantification has the same predicative
function expansion as ✱20·07. -/
def star_20_071
    (existential : ExistentialVocabulary signature (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (classSort resultOrder 0)) :=
  .sometimes existential body

theorem star_20_071_unfold
    (existential : ExistentialVocabulary signature (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    star_20_071 existential body = .sometimes existential body := rfl

/-! ## Class descriptions and functions of classes -/

/-- ✱20·072: a description of a class has contextual scope.  This is the
class-sort instance of ✱14·01, hence it introduces no description-valued term. -/
def star_20_072
    (existential : ExistentialVocabulary signature (classSort classOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0)
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (classSort classOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (condition : Formula signature real
      (classSort classOrder 0 :: apparent)
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (continuation : Formula signature real
      (classSort classOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (bindOrder identityBaseOrder
          (.function [classSort classOrder 0] identityBaseOrder identityExcess))
          (classSort classOrder 0)) scopeOrder)
        (classSort classOrder 0)) :=
  star_14_01 existential universal identityVocabulary equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction condition continuation

theorem star_20_072_unfold
    (existential : ExistentialVocabulary signature (classSort classOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0)
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (classSort classOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (condition : Formula signature real
      (classSort classOrder 0 :: apparent)
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (continuation : Formula signature real
      (classSort classOrder 0 :: apparent) scopeOrder) :
    star_20_072 existential universal identityVocabulary equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction condition continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (condition.rename (liftRenaming (fun v => .succ v)))
              (star_13_01 identityVocabulary (.apparent .zero)
                (.apparent (.succ .zero)))))
          continuation) := rfl

/-- Printed-to-AST reading of ✱20·072. -/
def star_20_072_reading
    (existential : ExistentialVocabulary signature (classSort classOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0)
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (classSort classOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess))
        (classSort classOrder 0)) scopeOrder))
    (condition : Formula signature real [classSort classOrder 0]
      (bindOrder identityBaseOrder
        (.function [classSort classOrder 0] identityBaseOrder identityExcess)))
    (continuation : Formula signature real [classSort classOrder 0]
      scopeOrder) : ClaimReading signature real where
  printed := "[(ια)(φα)] . f(ια)(φα) .=: (∃γ) : φα .≡ₐ. α = γ : fγ  Df"
  parsed := .assertion
    (star_20_072 existential universal identityVocabulary
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction condition continuation)

/-- ✱20·08: contextual abstraction over a class argument.  The witness is
a predicative unary function on the appropriate class sort. -/
def star_20_08
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (classSort classOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder)
        (.function [classSort classOrder 0] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (matrix.rename (liftRenaming (fun v => .succ v)))
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))))
      continuation)

theorem star_20_08_unfold
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (classSort classOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort classOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_20_08 existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (matrix.rename (liftRenaming (fun v => .succ v)))
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))))
          continuation) := rfl

/-- Printed-to-AST reading of ✱20·08. -/
def star_20_08_reading
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (universal : signature.Universal (classSort classOrder 0) resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (classSort classOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (classSort classOrder 0)) scopeOrder))
    (matrix : Formula signature real [classSort classOrder 0] resultOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "f{α(ψα)} .=: (∃φ) : ψα .≡ₐ. φ!α : f{φ!α}  Df"
  parsed := .assertion
    (star_20_08 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)

/-- ✱20·081: membership of a class argument in a predicative class
function is application, exactly as ✱20·02. -/
def star_20_081
    (predicate : Term signature real apparent
      (.function [classSort argumentOrder 0] resultOrder 0))
    (argument : Term signature real apparent (classSort argumentOrder 0)) :
    Formula signature real apparent resultOrder :=
  applyUnary predicate argument

theorem star_20_081_unfold
    (predicate : Term signature real apparent
      (.function [classSort argumentOrder 0] resultOrder 0))
    (argument : Term signature real apparent (classSort argumentOrder 0)) :
    star_20_081 predicate argument = applyUnary predicate argument := rfl

/-- Printed left member of ✱20·1, built through contextual class abstraction
✱20·01. -/
def star_20_1_left
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (continuation : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)) :=
  star_20_01 existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix continuation

/-- Printed right member of ✱20·1, built directly from its existential
predicative expansion rather than by reusing the class-abstraction term. -/
def star_20_1_right
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (continuation : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)) :=
  Formula.sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_20_1_left_unfold
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (continuation : Formula signature real [classSort resultOrder 0] scopeOrder) :
    star_20_1_left existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction matrix continuation =
      star_20_1_right existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction matrix continuation := rfl

/-- Audited catalogue reading of ✱20·1.  Its two printed members are built
independently; ✱20·01 proves that both unfold to the same tree. -/
def star_20_1_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real (.individual :: []) resultOrder)
    (continuation : Formula signature real
      (classSort resultOrder 0 :: []) scopeOrder) :
    ClaimReading signature real where
  printed := "⊢ : f{ẑ(ψz)} .≡ : (∃φ) : φ!x .≡ₓ. ψx : f{φ!ẑ}"
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_20_1_left existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_20_1_right existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation))

/-- ✱20·1, following PM's two printed citations: unfold ✱20·01, then use
✱4·2 on the resulting formula.  The predicative `!` is the zero excess in
`classSort resultOrder 0`.
`demonstration_provenance: follows-printed`. -/
theorem star_20_1
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real [.individual] resultOrder)
    (continuation : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_1_reading existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction finalNegation finalDisjunction matrix
      continuation).parsed := by
  have line1 := star_4_2 finalNegation finalDisjunction
    (star_20_1_right existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  change Derivation (.assertion (star_4_01 finalNegation finalDisjunction
    (star_20_1_left existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_20_1_right existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)))
  rw [star_20_1_left_unfold]
  exact line1

/-! ## The extensionality assertion ✱20·15

The two class abstractions are expanded independently by ✱20·01.  Their
equality is then the Leibniz identity of ✱13·01 at the predicative class
sort; it is not Lean equality and it is not replaced by a pointwise
definition.  The two implications have generally different syntactic
orders (`max p q` and `max q p`).  The small kernel-only arithmetic lemma
below identifies those computed orders before PM's conjunction definition is
used.
-/

section Star20Substitution

variable {signature : Signature} {real : Context}

private def star20ComposeSubstitution
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    Substitution signature real source target :=
  fun v => (sigma v).substitute tau

private theorem Term.star20_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (term : Term signature real source sort) :
    (term.substitute sigma).substitute tau =
      term.substitute (star20ComposeSubstitution sigma tau) := by
  cases term <;> rfl

private theorem Arguments.star20_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).substitute tau =
      arguments.substitute (star20ComposeSubstitution sigma tau) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.star20_substitute_substitute, ih]

private theorem Term.star20_weaken_substitute_lift
    (tau : Substitution signature real middle target)
    (term : Term signature real middle sort) :
    term.weaken.substitute (liftSubstitution (sort := binder) tau) =
      (term.substitute tau).weaken := by
  cases term <;> rfl

private theorem star20_lift_comp_pointwise
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      (liftSubstitution sigma v).substitute (liftSubstitution tau) =
        liftSubstitution (star20ComposeSubstitution sigma tau) v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact Term.star20_weaken_substitute_lift tau (sigma v)

private theorem star20_liftN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      (liftSubstitutionN binders sigma v).substitute
          (liftSubstitutionN binders tau) =
        liftSubstitutionN binders (star20ComposeSubstitution sigma tau) v := by
  induction binders with
  | nil =>
      intro sort v
      rfl
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v =>
          exact Eq.trans
            (Term.star20_weaken_substitute_lift
              (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

private theorem star20_lift_congr
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma v = liftSubstitution tau v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

private theorem star20_liftN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact star20_lift_congr _ _ ih

private theorem Term.star20_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source sort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

private theorem Arguments.star20_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.star20_substitute_of_pointwise sigma tau pointwise, ih]

private theorem Formula.star20_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.star20_substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.star20_substitute_of_pointwise sigma tau pointwise,
        Arguments.star20_substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih sigma tau pointwise)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      exact congrArg (Formula.always meaning)
        (ih (liftSubstitution sigma) (liftSubstitution tau)
          (star20_lift_congr sigma tau pointwise))
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (star20_liftN_congr parameters sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (star20_lift_congr sigma tau pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau)
          (star20_lift_congr sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (star20_lift_congr sigma tau pointwise)]

private theorem Formula.star20_rename_of_pointwise
    (rho tau : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = tau v)
    (formula : Formula signature real source order) :
    formula.rename rho = formula.rename tau := by
  let identity : Substitution signature real target target :=
    fun v => .apparent v
  have leftIdentity := Formula.substitute_eq_self (formula.rename rho)
    (by
      intro sort v
      exact rfl)
  have rightIdentity := Formula.substitute_eq_self (formula.rename tau)
    (by
      intro sort v
      exact rfl)
  have leftFusion := Formula.rename_substitute rho identity formula
  have rightFusion := Formula.rename_substitute tau identity formula
  have middle := Formula.star20_substitute_of_pointwise
    (substitutionAfterRenaming rho identity)
    (substitutionAfterRenaming tau identity)
    (by
      intro sort v
      exact congrArg Term.apparent (pointwise v)) formula
  exact Eq.trans leftIdentity.symm
    (Eq.trans leftFusion (Eq.trans middle (Eq.trans rightFusion.symm rightIdentity)))

private theorem Formula.star20_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).substitute tau =
      formula.substitute (star20ComposeSubstitution sigma tau) := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.star20_substitute_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.star20_substitute_substitute,
        Arguments.star20_substitute_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      have first := ih (liftSubstitution sigma) (liftSubstitution tau)
      have second := Formula.star20_substitute_of_pointwise
        (star20ComposeSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star20ComposeSubstitution sigma tau))
        (star20_lift_comp_pointwise sigma tau) body
      exact congrArg (Formula.always meaning) (Eq.trans first second)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      have matrixFirst := matrixIH (liftSubstitutionN parameters sigma)
        (liftSubstitutionN parameters tau)
      have matrixSecond := Formula.star20_substitute_of_pointwise
        (star20ComposeSubstitution (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau))
        (liftSubstitutionN parameters
          (star20ComposeSubstitution sigma tau))
        (star20_liftN_comp_pointwise parameters sigma tau) matrix
      have continuationFirst := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationSecond := Formula.star20_substitute_of_pointwise
        (star20ComposeSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star20ComposeSubstitution sigma tau))
        (star20_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextMatrix => Formula.incompleteScope kind parameters
          resultOrder excess scopeOrder nextMatrix
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans matrixFirst matrixSecond))
        (congrArg (Formula.incompleteScope kind parameters resultOrder excess
          scopeOrder
          (matrix.substitute (liftSubstitutionN parameters
            (star20ComposeSubstitution sigma tau))))
          (Eq.trans continuationFirst continuationSecond))
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      have conditionFirst := conditionIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have conditionSecond := Formula.star20_substitute_of_pointwise
        (star20ComposeSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star20ComposeSubstitution sigma tau))
        (star20_lift_comp_pointwise sigma tau) condition
      have continuationFirst := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationSecond := Formula.star20_substitute_of_pointwise
        (star20ComposeSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star20ComposeSubstitution sigma tau))
        (star20_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextCondition => Formula.descriptionScope sort
          conditionOrder scopeOrder nextCondition
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans conditionFirst conditionSecond))
        (congrArg (Formula.descriptionScope sort conditionOrder scopeOrder
          (condition.substitute
            (liftSubstitution (star20ComposeSubstitution sigma tau))))
          (Eq.trans continuationFirst continuationSecond))

end Star20Substitution

/-- Successor monotonicity, proved with the primitive recursor for `Nat.le`. -/
private theorem star20_succLeSucc {left right : Nat} :
    left ≤ right → left.succ ≤ right.succ :=
  fun proof => Nat.le.rec
    (motive := fun right _ => left.succ ≤ right.succ)
    Nat.le.refl (fun _ induction => Nat.le.step induction) proof

/-- Monotonicity of predecessor, again by primitive recursion. -/
private theorem star20_predLePred {left right : Nat} (proof : left ≤ right) :
    left.pred ≤ right.pred := by
  induction proof with
  | refl => exact Nat.le.refl
  | @step right proof induction =>
      cases right with
      | zero => exact induction
      | succ right => exact Nat.le.step induction

/-- Cancellation of successor for `Nat.le`, obtained from predecessor
monotonicity without a library theorem. -/
private theorem star20_leOfSuccLeSucc {left right : Nat}
    (proof : left.succ ≤ right.succ) : left ≤ right :=
  star20_predLePred proof

/-- Commutativity of the order join, proved only by primitive recursion.
The library theorem is deliberately not used on the object-calculus path. -/

private theorem star20_natMaxComm (left : Nat) :
    ∀ right : Nat, max left right = max right left :=
  Nat.rec
    (motive := fun left => ∀ right : Nat, max left right = max right left)
    (fun right => Nat.rec rfl (fun _ _ => rfl) right)
    (fun left induction right =>
      Nat.casesOn right rfl
        (fun right => by
          have inductionRight := induction right
          unfold Max.max Nat.instMax maxOfLe at inductionRight ⊢
          change (if left ≤ right then right else left) =
            (if right ≤ left then left else right) at inductionRight
          change (if left.succ ≤ right.succ then right.succ else left.succ) =
            (if right.succ ≤ left.succ then left.succ else right.succ)
          by_cases forward : left ≤ right
          · have forwardSucc := star20_succLeSucc forward
            rw [if_pos forwardSucc]
            by_cases reverse : right ≤ left
            · have reverseSucc := star20_succLeSucc reverse
              rw [if_pos reverseSucc]
              rw [if_pos forward, if_pos reverse] at inductionRight
              exact congrArg Nat.succ inductionRight
            · have reverseSucc : ¬ right.succ ≤ left.succ :=
                fun proof => reverse (star20_leOfSuccLeSucc proof)
              rw [if_neg reverseSucc]
          · have forwardSucc : ¬ left.succ ≤ right.succ :=
              fun proof => forward (star20_leOfSuccLeSucc proof)
            rw [if_neg forwardSucc]
            by_cases reverse : right ≤ left
            · have reverseSucc := star20_succLeSucc reverse
              rw [if_pos reverseSucc]
            · have reverseSucc : ¬ right.succ ≤ left.succ :=
                fun proof => reverse (star20_leOfSuccLeSucc proof)
              rw [if_neg reverseSucc]
              rw [if_neg forward, if_neg reverse] at inductionRight
              exact congrArg Nat.succ inductionRight))
    left

/-- Order of the pointwise equivalence `ψx ≡ₓ χx`. -/
def star_20_15_pointwiseOrder (resultOrder : Nat) : Nat :=
  bindOrder resultOrder .individual

/-- Order of Leibniz identity between predicative class representatives. -/
def star_20_15_identityOrder
    (resultOrder identityBaseOrder : Nat) : Nat :=
  bindOrder identityBaseOrder
    (.function [classSort resultOrder 0] identityBaseOrder 0)

/-- Order after expanding the inner abstraction `ẑ(χz)`. -/
def star_20_15_innerOrder
    (resultOrder identityBaseOrder : Nat) : Nat :=
  bindOrder
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_identityOrder resultOrder identityBaseOrder))
    (classSort resultOrder 0)

/-- Order after expanding both abstractions in their equality. -/
def star_20_15_classIdentityOrder
    (resultOrder identityBaseOrder : Nat) : Nat :=
  bindOrder
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_innerOrder resultOrder identityBaseOrder))
    (classSort resultOrder 0)

/-- Logical vocabulary for the exact contextual expansion of ✱20·15. -/
structure Star20ExtensionalityVocabulary
    (signature : Signature) (resultOrder identityBaseOrder : Nat) where
  pointUniversal : signature.Universal .individual resultOrder
  pointNegation : signature.Negation resultOrder
  pointDisjunction : signature.Disjunction resultOrder
  identity : IdentityVocabulary signature (classSort resultOrder 0)
    identityBaseOrder 0
  innerExistential : ExistentialVocabulary signature
    (classSort resultOrder 0)
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_identityOrder resultOrder identityBaseOrder))
  innerLeftNegation : signature.Negation
    (star_20_15_pointwiseOrder resultOrder)
  innerRightNegation : signature.Negation
    (star_20_15_identityOrder resultOrder identityBaseOrder)
  innerOuterNegation : signature.Negation
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_identityOrder resultOrder identityBaseOrder))
  innerConjunctionDisjunction : signature.Disjunction
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_identityOrder resultOrder identityBaseOrder))
  outerExistential : ExistentialVocabulary signature
    (classSort resultOrder 0)
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_innerOrder resultOrder identityBaseOrder))
  outerLeftNegation : signature.Negation
    (star_20_15_pointwiseOrder resultOrder)
  outerRightNegation : signature.Negation
    (star_20_15_innerOrder resultOrder identityBaseOrder)
  outerOuterNegation : signature.Negation
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_innerOrder resultOrder identityBaseOrder))
  outerConjunctionDisjunction : signature.Disjunction
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_innerOrder resultOrder identityBaseOrder))
  forwardNegation : signature.Negation
    (star_20_15_pointwiseOrder resultOrder)
  forwardDisjunction : signature.Disjunction
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_classIdentityOrder resultOrder identityBaseOrder))
  reverseNegation : signature.Negation
    (star_20_15_classIdentityOrder resultOrder identityBaseOrder)
  reverseDisjunction : signature.Disjunction
    (max (star_20_15_classIdentityOrder resultOrder identityBaseOrder)
      (star_20_15_pointwiseOrder resultOrder))
  finalNegation : signature.Negation
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_classIdentityOrder resultOrder identityBaseOrder))
  finalDisjunction : signature.Disjunction
    (max (star_20_15_pointwiseOrder resultOrder)
      (star_20_15_classIdentityOrder resultOrder identityBaseOrder))

/-- Left member of ✱20·15, with the subscript `x` represented by its
universal closure. -/
def star_20_15_pointwiseFormula
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :
    Formula signature real [] (star_20_15_pointwiseOrder resultOrder) :=
  .always vocabulary.pointUniversal
    (equivalence vocabulary.pointNegation vocabulary.pointDisjunction psi chi)

/-- Right member of ✱20·15.  Both incomplete class symbols are eliminated by
✱20·01, and the remaining equality is exactly ✱13·01. -/
def star_20_15_classIdentityFormula
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :
    Formula signature real []
      (star_20_15_classIdentityOrder resultOrder identityBaseOrder) :=
  star_20_01 vocabulary.outerExistential vocabulary.pointUniversal
    vocabulary.pointNegation vocabulary.pointDisjunction
    vocabulary.outerLeftNegation vocabulary.outerRightNegation
    vocabulary.outerOuterNegation vocabulary.outerConjunctionDisjunction psi
    (star_20_01 vocabulary.innerExistential vocabulary.pointUniversal
      vocabulary.pointNegation vocabulary.pointDisjunction
      vocabulary.innerLeftNegation vocabulary.innerRightNegation
      vocabulary.innerOuterNegation vocabulary.innerConjunctionDisjunction
      (chi.rename (liftRenaming
        (emptyRenaming (target := [classSort resultOrder 0]))))
      (star_13_01 vocabulary.identity
        (.apparent (.succ .zero)) (.apparent .zero)))

/-- The forward implication printed at ✱20·13. -/
def star_20_13_formula
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :=
  mixedImplication vocabulary.forwardNegation vocabulary.forwardDisjunction
    (star_20_15_pointwiseFormula vocabulary psi chi)
    (star_20_15_classIdentityFormula vocabulary psi chi)

/-- The reverse implication printed at ✱20·14. -/
def star_20_14_formula
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :=
  mixedImplication vocabulary.reverseNegation vocabulary.reverseDisjunction
    (star_20_15_classIdentityFormula vocabulary psi chi)
    (star_20_15_pointwiseFormula vocabulary psi chi)

/-- The reverse implication transported only across commutativity of its
computed order, so that PM's mono-order conjunction abbreviation applies. -/
def star_20_14_formulaAtForwardOrder
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :
    Formula signature real []
      (max (star_20_15_pointwiseOrder resultOrder)
        (star_20_15_classIdentityOrder resultOrder identityBaseOrder)) :=
  Eq.mp (congrArg (Formula signature real [])
      (star20_natMaxComm
        (star_20_15_classIdentityOrder resultOrder identityBaseOrder)
        (star_20_15_pointwiseOrder resultOrder)))
    (star_20_14_formula vocabulary psi chi)

/-- Exact heterogeneous mutual implication constituting ✱20·15. -/
def star_20_15_formula
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :=
  conjunction vocabulary.finalNegation vocabulary.finalDisjunction
    (star_20_13_formula vocabulary psi chi)
    (star_20_14_formulaAtForwardOrder vocabulary psi chi)

/-- Audited catalogue reading of ✱20·15. -/
def star_20_15_reading
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder) :
    ClaimReading signature real where
  printed := "✱20·15. ⊢ : ψx .≡ₓ. χx : ≡ : ẑ(ψz) = ẑ(χz)"
  parsed := .assertion (star_20_15_formula vocabulary psi chi)

/-- Transport of a derivation along equality of its computed ramified order. -/
private theorem star20_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder)
    (line : ⊢ᵣ formula) :
    ⊢ᵣ Eq.mp (congrArg (Formula signature real []) equality) formula := by
  cases equality
  exact line

private theorem star20_castSometimes
    (equality : sourceOrder = targetOrder)
    (existential : ExistentialVocabulary signature argument targetOrder)
    (body : Formula signature real [argument] sourceOrder) :
    Eq.mp (congrArg (Formula signature real [])
        (congrArg (fun order => bindOrder order argument) equality))
        (Formula.sometimes
          (Eq.mp (congrArg
            (ExistentialVocabulary signature argument) equality.symm)
            existential) body) =
      Formula.sometimes existential
        (Eq.mp (congrArg (Formula signature real [argument]) equality) body) := by
  cases equality
  rfl

private theorem star20_castWeakenInstantiate
    (equality : sourceOrder = targetOrder)
    (body : Formula signature real [argument] sourceOrder)
    (value : Term signature (argument :: real) [] argument) :
    ((Eq.mp (congrArg (Formula signature real [argument]) equality)
        body).weakenReal.instantiate value) =
      Eq.mp (congrArg (Formula signature (argument :: real) []) equality)
        (body.weakenReal.instantiate value) := by
  cases equality
  rfl

private theorem star20_castRoundTrip
    (equality : sourceOrder = targetOrder)
    (value : family sourceOrder) :
    Eq.mp (congrArg family equality.symm)
        (Eq.mp (congrArg family equality) value) = value := by
  cases equality
  rfl

/-- ✱20·15, assembled in PM's printed order from ✱20·13 and ✱20·14.

The two named hypotheses are retained because those two printed directions
are not yet reconstructed in the ramified calculus.  Thus this declaration
is an audited assertion, not an unconditional derivation.
`demonstration_provenance: follows-printed`. -/
theorem star_20_15
    (vocabulary : Star20ExtensionalityVocabulary signature resultOrder
      identityBaseOrder)
    (psi chi : Formula signature real [.individual] resultOrder)
    (star_20_13_hypothesis : ⊢ᵣ star_20_13_formula vocabulary psi chi)
    (star_20_14_hypothesis : ⊢ᵣ star_20_14_formula vocabulary psi chi) :
    Derivation (star_20_15_reading vocabulary psi chi).parsed := by
  have line1 := star_20_13_hypothesis
  have line2 := star_20_14_hypothesis
  have line3 : ⊢ᵣ star_20_14_formulaAtForwardOrder vocabulary psi chi :=
    star20_castAssertionOrder
      (star20_natMaxComm
        (star_20_15_classIdentityOrder resultOrder identityBaseOrder)
        (star_20_15_pointwiseOrder resultOrder))
      (star_20_14_formula vocabulary psi chi) line2
  have line4 := star_3_03 vocabulary.finalNegation vocabulary.finalDisjunction
    (star_20_13_formula vocabulary psi chi)
    (star_20_14_formulaAtForwardOrder vocabulary psi chi) line1 line3
  exact line4

/-! ## The eliminative theorem ✱20·3

The exact transformation needed below is a reducibility-scope transport
distinct from `star_10_35`.  After unfolding, ✱12·1 starts with
`.sometimes reducibilityExistential (unaryReducibilityMatrix ...)`, whereas
the required abstraction starts with `.sometimes abstractionExistential
(mixedConjunction ... (.always ...) continuation)`.  The two existential
vocabularies and the two bodies do not reduce to one another.  The theorem
therefore exposes this still-missing transport as a named local hypothesis.
-/

private def star20_existentialTransportFormula
    (existential : ExistentialVocabulary signature argument order)
    (scopeUniversal : signature.Universal argument
      (bindOrder order argument))
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [argument] order) :
    Formula signature real []
      (bindOrder (bindOrder order argument) argument) :=
  star_9_07 existential scopeUniversal disjunction
    ((Formula.neg existential.matrixNegation p).rename (fun v => .succ v))
    (q.rename implicationScopeHead)

private theorem star20_existentialTransport
    (existential : ExistentialVocabulary signature argument order)
    (scopeUniversal : signature.Universal argument
      (bindOrder order argument))
    (matrixDisjunction : signature.Disjunction order)
    (introductionDisjunction : signature.Disjunction
      (max order (bindOrder order argument)))
    (transportDisjunction : signature.Disjunction
      (max (bindOrder order argument) (bindOrder order argument)))
    (p q : Formula signature real [argument] order)
    (pointwise :
      let value : Term signature (argument :: real) [] argument := .real .zero
      Derivation (.assertion
        (implication existential.matrixNegation matrixDisjunction
          (p.weakenReal.instantiate value)
          (q.weakenReal.instantiate value))))
    (sourceLine : Derivation (.assertion (.sometimes existential p))) :
    Derivation (.assertion (.sometimes existential q)) := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let inner : Formula signature (argument :: real) [argument] order :=
    sameDisjunction matrixDisjunction
      ((Formula.neg existential.matrixNegation
        (p.weakenReal.instantiate value)).rename (fun v => .succ v))
      q.weakenReal
  have introduced := Derivation.star_9_1 existential
    existential.matrixNegation introductionDisjunction inner value
  have pointwiseLine : Derivation (.assertion
      (inner.instantiate value)) := by
    unfold inner Formula.instantiate
    rw [sameDisjunction_substitute, Formula.rename_substitute]
    rw [Formula.substitute_eq_self _ (by
      intro sort v
      exact nomatch v)]
    change Derivation (.assertion
      (implication existential.matrixNegation matrixDisjunction
        (p.weakenReal.instantiate value)
        (q.weakenReal.instantiate value)))
    exact pointwise
  have innerLine := Derivation.star_9_12 existential.matrixNegation
    introductionDisjunction pointwiseLine introduced
  let scopeBody := Formula.sometimes existential
    (sameDisjunction matrixDisjunction
      ((Formula.neg existential.matrixNegation p).rename
        (fun v => .succ v))
      (q.rename implicationScopeHead))
  let sourceSubstitution : Substitution signature (argument :: real)
      [argument] [] := instantiateSubstitution value
  let targetIdentity : Substitution signature (argument :: real)
      [argument] [argument] := fun v => .apparent v
  let emptySubstitution : Substitution signature (argument :: real)
      [] [argument] := fun v => nomatch v
  let leftFormula : Formula signature (argument :: real) [argument] order :=
    Formula.neg existential.matrixNegation
      (p.weakenReal (fresh := argument))
  have closedRename :
      (leftFormula.substitute sourceSubstitution).rename
          (emptyRenaming (target := [argument])) =
        (leftFormula.substitute sourceSubstitution).substitute
          emptySubstitution := by
    have identityLine := Formula.substitute_eq_self
      ((leftFormula.substitute sourceSubstitution).rename
        (emptyRenaming (target := [argument])))
      (by
        intro sort v
        exact rfl)
    have fusionLine := Formula.rename_substitute_of_pointwise
      (emptyRenaming (target := [argument])) targetIdentity
      emptySubstitution (by
        intro sort v
        exact nomatch v)
      (leftFormula.substitute sourceSubstitution)
    exact Eq.trans identityLine.symm fusionLine
  have leftScope :
      leftFormula.substitute
          (substitutionAfterRenaming (fun v => .succ v)
            (liftSubstitution sourceSubstitution)) =
        (leftFormula.substitute sourceSubstitution).rename
          (emptyRenaming (target := [argument])) := by
    have compositionLine := Formula.star20_substitute_substitute
      sourceSubstitution emptySubstitution leftFormula
    have pointwiseLine := Formula.star20_substitute_of_pointwise
      (substitutionAfterRenaming (fun v => .succ v)
        (liftSubstitution sourceSubstitution))
      (star20ComposeSubstitution sourceSubstitution emptySubstitution)
      (by
        intro sort v
        cases v with
        | zero => rfl
        | succ v => exact nomatch v)
      leftFormula
    exact Eq.trans pointwiseLine
      (Eq.trans compositionLine.symm closedRename.symm)
  have rightScope :
      q.weakenReal.substitute
          (substitutionAfterRenaming implicationScopeHead
            (liftSubstitution sourceSubstitution)) = q.weakenReal := by
    exact Formula.substitute_eq_self q.weakenReal (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v)
  have scopeAt : scopeBody.weakenReal.instantiate value =
      Formula.sometimes existential inner := by
    unfold leftFormula sourceSubstitution at leftScope rightScope
    have negationWeaken :
        (Formula.neg existential.matrixNegation p).weakenReal
            (fresh := argument) =
          Formula.neg existential.matrixNegation
            (p.weakenReal (fresh := argument)) := rfl
    unfold scopeBody inner Formula.sometimes Formula.instantiate
    change Formula.neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation
            ((sameDisjunction matrixDisjunction
              ((Formula.neg existential.matrixNegation p).rename
                (fun v => .succ v))
              (q.rename implicationScopeHead)).weakenReal.substitute
                (liftSubstitution (instantiateSubstitution value))))) = _
    rw [sameDisjunction_weakenReal, sameDisjunction_substitute,
      Formula.weakenReal_rename, Formula.weakenReal_rename,
      negationWeaken, Formula.rename_substitute, Formula.rename_substitute,
      leftScope, rightScope]
    have renameEquality := Formula.star20_rename_of_pointwise
      (emptyRenaming (target := [argument]))
      (fun v => .succ v)
      (by
        intro sort v
        exact nomatch v)
      (Formula.neg existential.matrixNegation
        (p.weakenReal.instantiate value))
    exact congrArg
      (fun left => Formula.neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation
            (sameDisjunction matrixDisjunction left q.weakenReal))))
      renameEquality
  have scopeLine := star_10_11 scopeUniversal scopeBody
    (Derivation.castAssertion scopeAt innerLine)
  letI : ImplicationReading existential.outerNegation transportDisjunction
      (.sometimes existential p)
      (star20_existentialTransportFormula existential scopeUniversal
        matrixDisjunction p q)
      (.sometimes existential q) := by
    refine {
      negated := star_9_02 existential.universal
        existential.matrixNegation p
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_02 existential.outerNegation
        existential existential.universal existential.matrixNegation p
    · unfold star_9_02 star20_existentialTransportFormula
      exact ImplicationDisjunction.star_9_07 existential.universal existential
        scopeUniversal matrixDisjunction (.neg existential.matrixNegation p) q
  have typedScopeLine : Derivation (.assertion
      (star20_existentialTransportFormula existential scopeUniversal
        matrixDisjunction p q)) := by
    change Derivation (.assertion (.always scopeUniversal scopeBody)) at scopeLine
    unfold scopeBody at scopeLine
    unfold star20_existentialTransportFormula star_9_07
    exact scopeLine
  exact Derivation.star_9_12 existential.outerNegation transportDisjunction
    sourceLine typedScopeLine

/-- The source candidate occupies the older slot and the target candidate
occupies the head slot while a scoped existential implication is built. -/
private def star20_sourceCandidate :
    Renaming [argument] [argument, argument] :=
  fun v => .succ v

private def star20_targetCandidate :
    Renaming [argument] [argument, argument] :=
  liftRenaming (emptyRenaming (target := [argument]))

private theorem Formula.star20_rename_eq_substitute
    (rho : Renaming source target)
    (formula : Formula signature real source order) :
    formula.rename rho =
      formula.substitute (fun v => .apparent (rho v)) := by
  let identity : Substitution signature real target target :=
    fun v => .apparent v
  have line1 := Formula.substitute_eq_self (formula.rename rho)
    (sigma := identity) (fun _ => rfl)
  have line2 := Formula.rename_substitute_of_pointwise rho identity
    (fun v => .apparent (rho v)) (fun _ => rfl) formula
  exact Eq.trans line1.symm line2

private theorem Formula.star20_sourceCandidate_sameWitness
    (formula : Formula signature real [argument] order)
    (value : Term signature (argument :: real) [] argument) :
    let sourceSubstitution : Substitution signature (argument :: real)
        [argument, argument] [argument] :=
      liftSubstitution (instantiateSubstitution value)
    let targetSubstitution : Substitution signature (argument :: real)
        [argument] [] := instantiateSubstitution value
    let combined : Substitution signature (argument :: real)
        [argument, argument] [] :=
      star20ComposeSubstitution sourceSubstitution targetSubstitution
    ((((formula.rename star20_sourceCandidate).rename
          (fun v => .succ v)).weakenReal).substitute
        (liftSubstitution (sort := scopeSort) combined)) =
      (formula.weakenReal.substitute targetSubstitution).rename
        (emptyRenaming (target := [scopeSort])) := by
  intro sourceSubstitution targetSubstitution combined
  rw [Formula.weakenReal_rename, Formula.weakenReal_rename,
    Formula.rename_substitute, Formula.rename_substitute,
    Formula.star20_rename_eq_substitute,
    Formula.star20_substitute_substitute]
  apply Formula.star20_substitute_of_pointwise
  intro sort v
  cases v with
  | zero =>
      unfold combined sourceSubstitution targetSubstitution
        star20_sourceCandidate star20ComposeSubstitution emptyRenaming
        substitutionAfterRenaming
      cases value with
      | real value => rfl
      | apparent value => exact nomatch value
      | symbol value => rfl
  | succ v => exact nomatch v

private theorem Formula.star20_targetCandidate_sameWitness
    (formula : Formula signature real [scopeSort, argument] order)
    (value : Term signature (argument :: real) [] argument) :
    let sourceSubstitution : Substitution signature (argument :: real)
        [argument, argument] [argument] :=
      liftSubstitution (instantiateSubstitution value)
    let targetSubstitution : Substitution signature (argument :: real)
        [argument] [] := instantiateSubstitution value
    let combined : Substitution signature (argument :: real)
        [argument, argument] [] :=
      star20ComposeSubstitution sourceSubstitution targetSubstitution
    ((formula.rename (liftRenaming star20_targetCandidate)).weakenReal.substitute
        (liftSubstitution (sort := scopeSort) combined)) =
      formula.weakenReal.substitute
        (liftSubstitution (sort := scopeSort) targetSubstitution) := by
  intro sourceSubstitution targetSubstitution combined
  rw [Formula.weakenReal_rename, Formula.rename_substitute]
  apply Formula.star20_substitute_of_pointwise
  intro sort v
  cases v with
  | zero => rfl
  | succ v =>
      cases v with
      | zero => rfl
      | succ v => exact nomatch v

private theorem star20_sometimes_rename
    (existential : ExistentialVocabulary signature argument order)
    (body : Formula signature real [argument] order) :
    (Formula.sometimes existential body).rename (fun v => .succ v) =
      Formula.sometimes existential (body.rename star20_targetCandidate) := by
  unfold Formula.sometimes
  have bodyRename := Formula.star20_rename_of_pointwise
    (liftRenaming (fun v => .succ v)) star20_targetCandidate
    (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v)
    body
  exact congrArg
    (fun next => Formula.neg existential.outerNegation
      (.always existential.universal
        (.neg existential.matrixNegation next)))
    bodyRename

private theorem star20_individualBindStable (order : Nat) :
    bindOrder (bindOrder order .individual) .individual =
      bindOrder order .individual := by
  cases order with
  | zero => rfl
  | succ order =>
      cases order with
      | zero => rfl
      | succ order => rfl

private theorem star20_uncastAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder)
    (line : ⊢ᵣ Eq.mp
      (congrArg (Formula signature real []) equality) formula) :
    ⊢ᵣ formula := by
  cases equality
  exact line

private theorem star20_mixedIdentity
    (rightEquality : rightOrder = leftOrder)
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder)
    (formulaEquality : Eq.mp
      (congrArg (Formula signature real []) rightEquality) right = left) :
    Derivation (.assertion
      (mixedImplication negation disjunction left right)) := by
  cases rightEquality
  cases formulaEquality
  let selfEquality : max rightOrder rightOrder = rightOrder :=
    natMaxSelf rightOrder
  let sameDisjunction : signature.Disjunction rightOrder :=
    Eq.mp (congrArg signature.Disjunction selfEquality) disjunction
  have line := star_2_08 negation sameDisjunction right
  have normalization := mixedImplication_normalizeSameOrder rfl rfl
    negation sameDisjunction right right
  have castLine := Derivation.castAssertion normalization line
  unfold sameDisjunction at castLine
  rw [star20_castRoundTrip selfEquality disjunction] at castLine
  apply star20_uncastAssertionOrder selfEquality
    (mixedImplication negation disjunction right right)
  change Derivation (.assertion
    (Eq.mp (congrArg (Formula signature real []) selfEquality)
      (mixedImplication negation disjunction right right)))
  exact castLine

private theorem star20_mixedSyll
    (orderEquality : max highOrder lowOrder = highOrder)
    (highNegation : signature.Negation highOrder)
    (lowNegation : signature.Negation lowOrder)
    (lowDisjunction : signature.Disjunction lowOrder)
    (mixedDisjunction : signature.Disjunction (max highOrder lowOrder))
    (p : Formula signature real [] highOrder)
    (q r : Formula signature real [] lowOrder)
    (leftLine : Derivation (.assertion
      (mixedImplication highNegation mixedDisjunction p q)))
    (rightLine : Derivation (.assertion
      (implication lowNegation lowDisjunction q r))) :
    Derivation (.assertion
      (mixedImplication highNegation mixedDisjunction p r)) := by
  let mixedNegation : signature.Negation (max highOrder lowOrder) :=
    Eq.mp (congrArg signature.Negation orderEquality.symm) highNegation
  let lowSelf : max lowOrder lowOrder = lowOrder := natMaxSelf lowOrder
  let lowPairNegation : signature.Negation (max lowOrder lowOrder) :=
    Eq.mp (congrArg signature.Negation lowSelf.symm) lowNegation
  let lowPairDisjunction : signature.Disjunction (max lowOrder lowOrder) :=
    Eq.mp (congrArg signature.Disjunction lowSelf.symm) lowDisjunction
  let pairSelf :
      max (max highOrder lowOrder) (max highOrder lowOrder) =
        max highOrder lowOrder := natMaxSelf (max highOrder lowOrder)
  let innerDisjunction : signature.Disjunction
      (max (max highOrder lowOrder) (max highOrder lowOrder)) :=
    Eq.mp (congrArg signature.Disjunction pairSelf.symm) mixedDisjunction
  let lowPair : max lowOrder (max highOrder lowOrder) =
      max highOrder lowOrder :=
    Eq.trans (congrArg (max lowOrder) orderEquality)
      (star20_natMaxComm lowOrder highOrder)
  let outerOrder :
      max (max lowOrder lowOrder)
          (max (max highOrder lowOrder) (max highOrder lowOrder)) =
        max highOrder lowOrder :=
    Eq.trans
      (congrArg
        (fun order => max order
          (max (max highOrder lowOrder) (max highOrder lowOrder)))
        lowSelf)
      (Eq.trans (congrArg (max lowOrder) pairSelf) lowPair)
  let outerDisjunction : signature.Disjunction
      (max (max lowOrder lowOrder)
        (max (max highOrder lowOrder) (max highOrder lowOrder))) :=
    Eq.mp (congrArg signature.Disjunction outerOrder.symm) mixedDisjunction
  have sum := Derivation.star_1_6 lowNegation lowPairDisjunction
    lowPairNegation
    mixedNegation mixedDisjunction mixedDisjunction innerDisjunction
    outerDisjunction (Formula.neg highNegation p) q r
  have rightExpected : Derivation (.assertion
      (mixedImplication lowNegation lowPairDisjunction q r)) := by
    have normalization := mixedImplication_normalizeSameOrder rfl rfl
      lowNegation lowDisjunction q r
    have castLine := Derivation.castAssertion normalization.symm rightLine
    apply star20_uncastAssertionOrder lowSelf
      (mixedImplication lowNegation lowPairDisjunction q r)
    change Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) lowSelf)
        (mixedImplication lowNegation lowPairDisjunction q r)))
    exact castLine
  have remaining := Derivation.star_9_12 lowPairNegation outerDisjunction
    rightExpected sum
  exact Derivation.star_9_12 mixedNegation innerDisjunction
    leftLine remaining

/-- If one occurrence of a premise proves a second occurrence and also proves
a conclusion, the premise proves their conjunction.  The two premise
occurrences are distinct propositional variables here, so their negation
vocabularies need not coincide. -/
private theorem star20_ternaryConjunction
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (linePQ : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryQ))))
    (linePR : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryR)))) :
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (PM.Elementary.imp MixedOrder.ternaryP
          (PM.Elementary.conj MixedOrder.ternaryQ MixedOrder.ternaryR)))) := by
  let elementaryProduct :=
    PM.Elementary.conj MixedOrder.ternaryQ MixedOrder.ternaryR
  let forward := PM.Elementary.imp
    (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryR)
    (PM.Elementary.imp MixedOrder.ternaryP elementaryProduct)
  let backward := PM.Elementary.imp
    (PM.Elementary.imp MixedOrder.ternaryP elementaryProduct)
    (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryR)
  let source := PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryQ
  let target := PM.Elementary.imp MixedOrder.ternaryP elementaryProduct
  let transformer := PM.Elementary.imp source forward
  have elementaryTransformer : PM.Derivation transformer := by
    have line44 := PM.FirstEdition.Volume1.Star5.star_5_44
      MixedOrder.ternaryP MixedOrder.ternaryQ MixedOrder.ternaryR
    have projection := PM.FirstEdition.Volume1.Star3.star_3_26
      forward backward
    have composition := PM.FirstEdition.Volume1.Star2.star_2_05
      source (PM.Elementary.equiv
        (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryR)
        (PM.Elementary.imp MixedOrder.ternaryP elementaryProduct)) forward
    exact PM.Derivation.detach line44
      (PM.Derivation.detach projection composition)
  have transported := MixedOrder.ternaryTransport negation disjunction p q r
    elementaryTransformer
  have middle := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pqr)
    (negation.meaning .pq) (disjunction.meaning .pqr)
    (MixedOrder.ternaryInterpret negation disjunction p q r source)
    (MixedOrder.ternaryInterpret negation disjunction p q r forward)
    linePQ transported
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pr .pqr)
    (negation.meaning .pr) (disjunction.meaning .pqr)
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (PM.Elementary.imp MixedOrder.ternaryP MixedOrder.ternaryR))
    (MixedOrder.ternaryInterpret negation disjunction p q r target)
    linePR middle

private theorem star20_scopedExistentialTransport_unused
    (existential : ExistentialVocabulary signature argument order)
    (scopeUniversal : signature.Universal argument
      (bindOrder order argument))
    (introductionDisjunction : signature.Disjunction
      (max order (bindOrder order argument)))
    (transportDisjunction : signature.Disjunction
      (max (bindOrder order argument) (bindOrder order argument)))
    (p q : Formula signature real [argument] order)
    (inner : Formula signature real [argument, argument] order)
    (innerReading : ImplicationDisjunction signature real
      ((Formula.neg existential.matrixNegation p).rename
        star20_sourceCandidate)
      (q.rename star20_targetCandidate) inner)
    (sameWitnessLine :
      let value : Term signature (argument :: real) [] argument := .real .zero
      let sourceSubstitution : Substitution signature (argument :: real)
          [argument, argument] [argument] :=
        liftSubstitution (instantiateSubstitution value)
      Derivation (.assertion
        ((inner.weakenReal.substitute sourceSubstitution).instantiate value)))
    (sourceLine : Derivation (.assertion (.sometimes existential p))) :
    Derivation (.assertion (.sometimes existential q)) := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let sourceSubstitution : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution value)
  let innerAtSource : Formula signature (argument :: real) [argument] order :=
    inner.weakenReal.substitute sourceSubstitution
  have introduced := Derivation.star_9_1 existential
    existential.matrixNegation introductionDisjunction innerAtSource value
  have innerLine : Derivation (.assertion
      (.sometimes existential innerAtSource)) :=
    Derivation.star_9_12 existential.matrixNegation
      introductionDisjunction sameWitnessLine introduced
  let outerBody : Formula signature real [argument]
      (bindOrder order argument) :=
    .sometimes existential inner
  have outerAt : outerBody.weakenReal.instantiate value =
      .sometimes existential innerAtSource := by
    rfl
  have scopeLine := star_10_11 scopeUniversal outerBody
    (Derivation.castAssertion outerAt innerLine)
  let scopeFormula : Formula signature real []
      (bindOrder (bindOrder order argument) argument) :=
    .always scopeUniversal outerBody
  letI : ImplicationReading existential.outerNegation transportDisjunction
      (.sometimes existential p) scopeFormula (.sometimes existential q) := by
    refine {
      negated := star_9_02 existential.universal
        existential.matrixNegation p
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_02 existential.outerNegation
        existential existential.universal existential.matrixNegation p
    · unfold scopeFormula outerBody
      apply ImplicationDisjunction.star_9_03 existential.universal
        scopeUniversal
      have innerScope := ImplicationDisjunction.star_9_06 existential existential
        ((Formula.neg existential.matrixNegation p))
        (q.rename star20_targetCandidate) inner innerReading
      exact Eq.mp (congrArg
        (fun target => ImplicationDisjunction signature real
          (Formula.neg existential.matrixNegation p) target
          (Formula.sometimes existential inner))
        (star20_sometimes_rename existential q).symm) innerScope
  have typedScopeLine : Derivation (.assertion scopeFormula) := by
    unfold scopeFormula
    exact scopeLine
  exact Derivation.star_9_12 existential.outerNegation transportDisjunction
    sourceLine typedScopeLine

private theorem star20_equivalenceSymmetry
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Derivation (.assertion (implication negation disjunction
      (equivalence negation disjunction p q)
      (equivalence negation disjunction q p))) := by
  have line1 := star_4_21 negation disjunction p q
  exact Derivation.star_9_12_same negation disjunction line1
    (star_3_26 negation disjunction
      (implication negation disjunction
        (equivalence negation disjunction p q)
        (equivalence negation disjunction q p))
      (implication negation disjunction
        (equivalence negation disjunction q p)
        (equivalence negation disjunction p q)))

private theorem star20_equivalence_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (equivalence negation disjunction left right).weakenReal
      (fresh := fresh) =
    equivalence negation disjunction left.weakenReal right.weakenReal := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).weakenReal))
      (.neg negation
        ((implication negation disjunction right left).weakenReal))) = _
  rw [implication_weakenReal, implication_weakenReal]

private theorem star20_equivalence_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (equivalence negation disjunction left right).substitute sigma =
      equivalence negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).substitute
        sigma) = _
  rw [sameDisjunction_substitute]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).substitute sigma))
      (.neg negation
        ((implication negation disjunction right left).substitute sigma))) = _
  rw [implication_substitute, implication_substitute]

private theorem star20_mixedImplication_weakenReal
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (mixedImplication negation disjunction left right).weakenReal
      (fresh := fresh) =
    mixedImplication negation disjunction left.weakenReal right.weakenReal := by
  rfl

private theorem star20_mixedImplication_substitute
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real source leftOrder)
    (right : Formula signature real source rightOrder)
    (sigma : Substitution signature real source target) :
    (mixedImplication negation disjunction left right).substitute sigma =
      mixedImplication negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  rfl

private theorem star20_always_weakenReal
    (universal : signature.Universal argument order)
    (body : Formula signature real (argument :: apparent) order) :
    (Formula.always universal body).weakenReal (fresh := fresh) =
      Formula.always universal body.weakenReal := by
  rfl

private def star20_castImplicationDisjunctionResult
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder)
    (result : Formula signature real apparent sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left right
      (Eq.mp (congrArg (Formula signature real apparent) equality) result) := by
  cases equality
  exact reading

private theorem star20_castSameWitness
    (equality : sourceOrder = targetOrder)
    (inner : Formula signature real [argument, argument] sourceOrder)
    (value : Term signature (argument :: real) [] argument) :
    let sourceSubstitution : Substitution signature (argument :: real)
        [argument, argument] [argument] :=
      liftSubstitution (instantiateSubstitution value)
    (((Eq.mp (congrArg (Formula signature real [argument, argument])
        equality) inner).weakenReal.substitute sourceSubstitution).instantiate
      value) =
      Eq.mp (congrArg (Formula signature (argument :: real) []) equality)
        ((inner.weakenReal.substitute sourceSubstitution).instantiate value) := by
  cases equality
  rfl

/-- Reducibility supplies `ψ ≡ φ!`; the contextual abstraction uses
the reverse orientation.  This is the two-scope transport of ✱4·21: first
under the individual universal and then under the candidate existential. -/
private theorem star20_reducibilityOrientation
    (existential : ExistentialVocabulary signature
      (classSort resultOrder 0) (bindOrder resultOrder .individual))
    (candidateScopeUniversal : signature.Universal
      (classSort resultOrder 0)
      (bindOrder (bindOrder resultOrder .individual)
        (classSort resultOrder 0)))
    (orientationUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (mixedDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (introductionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual)
        (bindOrder (bindOrder resultOrder .individual)
          (classSort resultOrder 0))))
    (transportDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder resultOrder .individual)
          (classSort resultOrder 0))
        (bindOrder (bindOrder resultOrder .individual)
          (classSort resultOrder 0))))
    (matrix : Formula signature real [.individual] resultOrder)
    (sourceLine : Derivation (.assertion
      (star_12_1_formula existential universal equivalenceNegation
        equivalenceDisjunction matrix))) :
    Derivation (.assertion (.sometimes existential
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v))))))) := by
  let highOrder := bindOrder resultOrder .individual
  let pairEquality : max highOrder resultOrder = highOrder :=
    Eq.trans (bindOrderMaxRight resultOrder resultOrder .individual)
      (congrArg (fun order => bindOrder order .individual)
        (natMaxSelf resultOrder))
  let stableEquality : bindOrder highOrder .individual = highOrder :=
    star20_individualBindStable resultOrder
  let matrixWithCandidate : Formula signature real
      [.individual, classSort resultOrder 0] resultOrder :=
    matrix.rename (liftRenaming
      (emptyRenaming (target := [classSort resultOrder 0])))
  let predicateAtPoint : Formula signature real
      [.individual, classSort resultOrder 0] resultOrder :=
    applyUnary (.apparent (.succ .zero)) (.apparent .zero)
  let reducibilityBody : Formula signature real
      [.individual, classSort resultOrder 0] resultOrder :=
    equivalence equivalenceNegation equivalenceDisjunction
      matrixWithCandidate predicateAtPoint
  let abstractionBody : Formula signature real
      [.individual, classSort resultOrder 0] resultOrder :=
    equivalence equivalenceNegation equivalenceDisjunction
      predicateAtPoint matrixWithCandidate
  let p : Formula signature real [classSort resultOrder 0] highOrder :=
    .always universal reducibilityBody
  let q : Formula signature real [classSort resultOrder 0] highOrder :=
    .always universal abstractionBody
  let qBodyAtTarget := abstractionBody.rename
    (liftRenaming star20_targetCandidate)
  let orientationUniversalAtPair : signature.Universal .individual
      (max highOrder resultOrder) :=
    Eq.mp (congrArg (signature.Universal .individual)
      pairEquality.symm) orientationUniversal
  let innerRaw := star_9_04 orientationUniversalAtPair mixedDisjunction
    ((Formula.neg existential.matrixNegation p).rename
      star20_sourceCandidate) qBodyAtTarget
  let innerOrderEquality :
      bindOrder (max highOrder resultOrder) .individual = highOrder :=
    Eq.trans
      (congrArg (fun order => bindOrder order .individual) pairEquality)
      stableEquality
  let inner : Formula signature real
      [classSort resultOrder 0, classSort resultOrder 0] highOrder :=
    Eq.mp (congrArg (Formula signature real
      [classSort resultOrder 0, classSort resultOrder 0])
      innerOrderEquality) innerRaw
  have innerReading : ImplicationDisjunction signature real
      ((Formula.neg existential.matrixNegation p).rename
        star20_sourceCandidate)
      (q.rename star20_targetCandidate) inner := by
    have rawReading : ImplicationDisjunction signature real
        ((Formula.neg existential.matrixNegation p).rename
          star20_sourceCandidate)
        (.always universal qBodyAtTarget) innerRaw := by
      apply ImplicationDisjunction.star_9_04 universal
        orientationUniversalAtPair
      exact ImplicationDisjunction.star_1_01 mixedDisjunction
        (((Formula.neg existential.matrixNegation p).rename
          star20_sourceCandidate).rename
          (fun v => .succ v))
        qBodyAtTarget
    have qRename : q.rename star20_targetCandidate =
        Formula.always universal qBodyAtTarget := by
      rfl
    have rightReading := Eq.mp (congrArg
      (fun right => ImplicationDisjunction signature real
        ((Formula.neg existential.matrixNegation p).rename
          star20_sourceCandidate) right innerRaw)
      qRename.symm) rawReading
    exact star20_castImplicationDisjunctionResult innerOrderEquality
      ((Formula.neg existential.matrixNegation p).rename
        star20_sourceCandidate)
      (q.rename star20_targetCandidate) innerRaw rightReading
  have sameWitnessLine :
      let value : Term signature
          (classSort resultOrder 0 :: real) []
          (classSort resultOrder 0) := .real .zero
      let sourceSubstitution : Substitution signature
          (classSort resultOrder 0 :: real)
          [classSort resultOrder 0, classSort resultOrder 0]
          [classSort resultOrder 0] :=
        liftSubstitution (instantiateSubstitution value)
      Derivation (.assertion
        ((inner.weakenReal.substitute sourceSubstitution).instantiate value)) := by
    let individual : Term signature
        (.individual :: classSort resultOrder 0 :: real) [] .individual :=
      .real .zero
    let predicateMatrix : Formula signature
        (classSort resultOrder 0 :: real) [.individual] resultOrder :=
      applyUnary
        (.real (.zero : Var (classSort resultOrder 0 :: real)
          (classSort resultOrder 0)))
        (.apparent .zero)
    have specialization := star_10_43 universal equivalenceNegation
      equivalenceDisjunction existential.matrixNegation mixedDisjunction
      matrix.weakenReal.weakenReal predicateMatrix.weakenReal individual
    unfold star_10_43_reading at specialization
    unfold Formula.instantiate at specialization
    rw [star20_equivalence_substitute] at specialization
    let matrixAt := matrix.weakenReal.weakenReal.instantiate individual
    let predicateAt := predicateMatrix.weakenReal.instantiate individual
    have specializationExpected : Derivation (.assertion
        (mixedImplication existential.matrixNegation mixedDisjunction
          (Formula.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              matrix.weakenReal.weakenReal predicateMatrix.weakenReal))
          (equivalence equivalenceNegation equivalenceDisjunction
            matrixAt predicateAt))) := by
      unfold matrixAt predicateAt Formula.instantiate
      exact specialization
    have reversal := star20_equivalenceSymmetry equivalenceNegation
      equivalenceDisjunction matrixAt predicateAt
    have composed := star20_mixedSyll pairEquality
      existential.matrixNegation equivalenceNegation equivalenceDisjunction
      mixedDisjunction
      (Formula.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          matrix.weakenReal.weakenReal predicateMatrix.weakenReal))
      (equivalence equivalenceNegation equivalenceDisjunction
        matrixAt predicateAt)
      (equivalence equivalenceNegation equivalenceDisjunction
        predicateAt matrixAt)
      specializationExpected reversal
    let scopeBody := mixedImplication existential.matrixNegation
      mixedDisjunction
      ((Formula.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          matrix.weakenReal predicateMatrix)).rename (fun v => .succ v))
      (equivalence equivalenceNegation equivalenceDisjunction
        predicateMatrix matrix.weakenReal)
    have scopeAt : scopeBody.weakenReal.instantiate individual =
        mixedImplication existential.matrixNegation mixedDisjunction
          (Formula.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              matrix.weakenReal.weakenReal predicateMatrix.weakenReal))
          (equivalence equivalenceNegation equivalenceDisjunction
            predicateAt matrixAt) := by
      unfold Formula.instantiate
      rw [star20_mixedImplication_weakenReal,
        star20_mixedImplication_substitute,
        Formula.closed_weakenReal_instantiateSubstitution,
        star20_always_weakenReal]
      have leftWeaken := star20_equivalence_weakenReal
        (fresh := .individual)
        equivalenceNegation equivalenceDisjunction
        matrix.weakenReal predicateMatrix
      have rightWeaken := star20_equivalence_weakenReal
        (fresh := .individual)
        equivalenceNegation equivalenceDisjunction
        predicateMatrix matrix.weakenReal
      rw [leftWeaken, rightWeaken, star20_equivalence_substitute]
      unfold predicateAt matrixAt Formula.instantiate
      rfl
    have scopedLine := star_10_11 orientationUniversalAtPair scopeBody
      (Derivation.castAssertion scopeAt composed)
    have innerAtSameCandidate :
        ((innerRaw.weakenReal.substitute
          (liftSubstitution (instantiateSubstitution
            (.real (.zero : Var (classSort resultOrder 0 :: real)
              (classSort resultOrder 0)))))).instantiate
            (.real (.zero : Var (classSort resultOrder 0 :: real)
              (classSort resultOrder 0)))) =
          .always orientationUniversalAtPair scopeBody := by
      unfold innerRaw star_9_04 Formula.instantiate
      rw [Formula.star20_substitute_substitute]
      let candidate : Term signature (classSort resultOrder 0 :: real) []
          (classSort resultOrder 0) := .real .zero
      let sourceSubstitution : Substitution signature
          (classSort resultOrder 0 :: real)
          [classSort resultOrder 0, classSort resultOrder 0]
          [classSort resultOrder 0] :=
        liftSubstitution (instantiateSubstitution candidate)
      let targetSubstitution : Substitution signature
          (classSort resultOrder 0 :: real) [classSort resultOrder 0] [] :=
        instantiateSubstitution candidate
      let combined : Substitution signature (classSort resultOrder 0 :: real)
          [classSort resultOrder 0, classSort resultOrder 0] [] :=
        star20ComposeSubstitution sourceSubstitution targetSubstitution
      change Formula.always orientationUniversalAtPair
          (((Formula.disj mixedDisjunction
            ((Formula.neg existential.matrixNegation p).rename
              star20_sourceCandidate |>.rename (fun v => .succ v))
            qBodyAtTarget).weakenReal).substitute
              (liftSubstitution (sort := .individual) combined)) =
        Formula.always orientationUniversalAtPair scopeBody
      unfold qBodyAtTarget
      change Formula.always orientationUniversalAtPair
          (.disj mixedDisjunction
            ((((Formula.neg existential.matrixNegation p).rename
              star20_sourceCandidate).rename
                (fun v => .succ v)).weakenReal.substitute
                  (liftSubstitution (sort := .individual) combined))
            ((abstractionBody.rename
              (liftRenaming star20_targetCandidate)).weakenReal.substitute
                (liftSubstitution (sort := .individual) combined))) =
        Formula.always orientationUniversalAtPair scopeBody
      rw [Formula.star20_sourceCandidate_sameWitness
          (scopeSort := .individual)
          (Formula.neg existential.matrixNegation p) candidate,
        Formula.star20_targetCandidate_sameWitness abstractionBody candidate]
      have matrixCandidateAt :
          matrixWithCandidate.weakenReal.substitute
              (liftSubstitution targetSubstitution) =
            matrix.weakenReal := by
        unfold matrixWithCandidate
        rw [Formula.weakenReal_rename, Formula.rename_substitute]
        apply Formula.substitute_eq_self
        intro sort v
        cases v with
        | zero => rfl
        | succ v => exact nomatch v
      have predicatePointAt :
          predicateAtPoint.weakenReal.substitute
              (liftSubstitution targetSubstitution) =
            predicateMatrix := by
        unfold predicateAtPoint predicateMatrix targetSubstitution
          applyUnary
        rfl
      have pAt : p.weakenReal.substitute targetSubstitution =
          Formula.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              matrix.weakenReal predicateMatrix) := by
        unfold p reducibilityBody
        rw [star20_always_weakenReal,
          substitute_always,
          star20_equivalence_weakenReal,
          star20_equivalence_substitute,
          matrixCandidateAt, predicatePointAt]
      have sourceAt :
          ((Formula.neg existential.matrixNegation p).weakenReal.substitute
              targetSubstitution).rename
                (emptyRenaming (target := [.individual])) =
            Formula.neg existential.matrixNegation
              ((Formula.always universal
                (equivalence equivalenceNegation equivalenceDisjunction
                  matrix.weakenReal predicateMatrix)).rename
                    (fun v => .succ v)) := by
        change Formula.neg existential.matrixNegation
            ((p.weakenReal.substitute targetSubstitution).rename
              (emptyRenaming (target := [.individual]))) = _
        rw [pAt]
        exact congrArg (Formula.neg existential.matrixNegation)
          (Formula.star20_rename_of_pointwise
            (emptyRenaming (target := [.individual]))
            (fun v => .succ v)
            (by
              intro sort v
              exact nomatch v)
            (Formula.always universal
              (equivalence equivalenceNegation equivalenceDisjunction
                matrix.weakenReal predicateMatrix)))
      have targetAt :
          abstractionBody.weakenReal.substitute
              (liftSubstitution targetSubstitution) =
            equivalence equivalenceNegation equivalenceDisjunction
              predicateMatrix matrix.weakenReal := by
        unfold abstractionBody
        rw [star20_equivalence_weakenReal,
          star20_equivalence_substitute,
          predicatePointAt, matrixCandidateAt]
      rw [sourceAt, targetAt]
      unfold scopeBody mixedImplication
      rfl
    change Derivation (.assertion
      (((Eq.mp (congrArg (Formula signature real
          [classSort resultOrder 0, classSort resultOrder 0])
          innerOrderEquality) innerRaw).weakenReal.substitute
        (liftSubstitution (instantiateSubstitution
          (.real (.zero : Var (classSort resultOrder 0 :: real)
            (classSort resultOrder 0)))))).instantiate
          (.real (.zero : Var (classSort resultOrder 0 :: real)
            (classSort resultOrder 0)))))
    rw [star20_castSameWitness innerOrderEquality innerRaw
      (.real (.zero : Var (classSort resultOrder 0 :: real)
        (classSort resultOrder 0)))]
    apply star20_castAssertionOrder innerOrderEquality
    change Derivation (.assertion
      (.always orientationUniversalAtPair scopeBody)) at scopedLine
    exact Derivation.castAssertion innerAtSameCandidate scopedLine
  have oriented := star20_scopedExistentialTransport_unused existential
    candidateScopeUniversal introductionDisjunction transportDisjunction
    p q inner innerReading sameWitnessLine sourceLine
  have matrixRename : matrixWithCandidate =
      matrix.rename (liftRenaming (fun v => .succ v)) := by
    exact Formula.star20_rename_of_pointwise
      (liftRenaming (emptyRenaming
        (target := [classSort resultOrder 0])))
      (liftRenaming (fun v => .succ v))
      (by
        intro sort v
        cases v with
        | zero => rfl
        | succ v => exact nomatch v)
      matrix
  have targetEquality : Formula.sometimes existential q =
      Formula.sometimes existential
        (.always universal
          (equivalence equivalenceNegation equivalenceDisjunction
            (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
            (matrix.rename (liftRenaming (fun v => .succ v))))) := by
    unfold q abstractionBody predicateAtPoint
    exact congrArg
      (fun nextMatrix => Formula.sometimes existential
        (.always universal
          (equivalence equivalenceNegation equivalenceDisjunction
            (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
            nextMatrix)))
      matrixRename
  exact Derivation.castAssertion targetEquality.symm oriented

/-- Existential transport when the implication between the two candidate
matrices already has a quantified-scope reading.  The outer disjunction is
read successively by ✱9·03 and ✱9·06; the latter keeps the same witness.
Thus the innermost formula need not be a raw disjunction, only a certified
implication in PM's sense. -/
private theorem star20_scopedExistentialTransport
    (existential : ExistentialVocabulary signature argument order)
    (scopeUniversal : signature.Universal argument
      (bindOrder order argument))
    (introductionDisjunction : signature.Disjunction
      (max order (bindOrder order argument)))
    (transportDisjunction : signature.Disjunction
      (max (bindOrder order argument) (bindOrder order argument)))
    (p q : Formula signature real [argument] order)
    (inner : Formula signature real [argument, argument] order)
    (innerReading : ImplicationDisjunction signature real
      ((Formula.neg existential.matrixNegation p).rename
        star20_sourceCandidate)
      (q.rename star20_targetCandidate) inner)
    (sameWitnessLine :
      let value : Term signature (argument :: real) [] argument := .real .zero
      let sourceSubstitution : Substitution signature (argument :: real)
          [argument, argument] [argument] :=
        liftSubstitution (instantiateSubstitution value)
      Derivation (.assertion
        ((inner.weakenReal.substitute sourceSubstitution).instantiate value)))
    (sourceLine : Derivation (.assertion (.sometimes existential p))) :
    Derivation (.assertion (.sometimes existential q)) := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let sourceSubstitution : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution value)
  let innerAtSource : Formula signature (argument :: real) [argument] order :=
    inner.weakenReal.substitute sourceSubstitution
  have introduced := Derivation.star_9_1 existential
    existential.matrixNegation introductionDisjunction innerAtSource value
  have innerLine : Derivation (.assertion
      (.sometimes existential innerAtSource)) :=
    Derivation.star_9_12 existential.matrixNegation
      introductionDisjunction sameWitnessLine introduced
  let outerBody : Formula signature real [argument]
      (bindOrder order argument) :=
    .sometimes existential inner
  have outerAt : outerBody.weakenReal.instantiate value =
      .sometimes existential innerAtSource := by
    rfl
  have scopeLine := star_10_11 scopeUniversal outerBody
    (Derivation.castAssertion outerAt innerLine)
  let scopeFormula : Formula signature real []
      (bindOrder (bindOrder order argument) argument) :=
    .always scopeUniversal outerBody
  letI : ImplicationReading existential.outerNegation transportDisjunction
      (.sometimes existential p) scopeFormula (.sometimes existential q) := by
    refine {
      negated := star_9_02 existential.universal
        existential.matrixNegation p
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_02 existential.outerNegation
        existential existential.universal existential.matrixNegation p
    · unfold scopeFormula outerBody
      apply ImplicationDisjunction.star_9_03 existential.universal
        scopeUniversal
      have innerScope := ImplicationDisjunction.star_9_06 existential existential
        ((Formula.neg existential.matrixNegation p))
        (q.rename star20_targetCandidate) inner innerReading
      exact Eq.mp (congrArg
        (fun target => ImplicationDisjunction signature real
          (Formula.neg existential.matrixNegation p) target
          (Formula.sometimes existential inner))
        (star20_sometimes_rename existential q).symm) innerScope
  have typedScopeLine : Derivation (.assertion scopeFormula) := by
    unfold scopeFormula
    exact scopeLine
  exact Derivation.star_9_12 existential.outerNegation transportDisjunction
    sourceLine typedScopeLine

/-- The predicative function matrix used when ✱10·43 specializes the
pointwise equivalence at `x`. -/
def star_20_3_predicateMatrix
    (_matrix : Formula signature real [.individual] resultOrder) :
    Formula signature (classSort resultOrder 0 :: real) [.individual]
      resultOrder :=
  applyUnary
    (.real (.zero : Var (classSort resultOrder 0 :: real)
      (classSort resultOrder 0)))
    (.apparent .zero)

/-- The exact ✱10·43 instance occurring on PM's third displayed line in the
proof of ✱20·3. -/
def star_20_3_transportFormula
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature (classSort resultOrder 0 :: real) []
      (max (bindOrder resultOrder .individual) resultOrder) :=
  mixedImplication outerNegation outerDisjunction
    (.always universal
      (equivalence equivalenceNegation equivalenceDisjunction
        (star_20_3_predicateMatrix matrix) matrix.weakenReal))
    ((equivalence equivalenceNegation equivalenceDisjunction
      (star_20_3_predicateMatrix matrix) matrix.weakenReal).instantiate
        x.weakenReal)

/-- The continuation obtained from the membership definition ✱20·02.  Since
class abstraction is contextual, this continuation is part of the expansion
of the whole displayed equivalence. -/
def star_20_3_continuation
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature real [classSort resultOrder 0] resultOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (star_20_02 (.apparent .zero) x.weaken)
    ((matrix.instantiate x).rename
      (emptyRenaming (target := [classSort resultOrder 0])))

/-- Object formula of ✱20·3 after the contextual definition ✱20·01. -/
def star_20_3_formula
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)) :=
  star_20_01 existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix
    (star_20_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x)

/-- Audited catalogue reading of ✱20·3. -/
def star_20_3_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    ClaimReading signature real where
  printed := "✱20·3. ⊢ : x ε ẑ(ψz) .≡ . ψx"
  parsed := .assertion (star_20_3_formula existential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix x)


/-- ✱20·3, following the printed ✱20·1·02, ✱10·43·35, ✱12·1 chain.

The object theorem ✱10·35 is now present.  The explicit hypothesis below is
the stronger contextual bridge that also consumes the real-context ✱10·43
consequence before producing the existential implication used with ✱12·1.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_20_3
    (abstractionExistential : ExistentialVocabulary signature
      (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
    (reducibilityExistential : ExistentialVocabulary signature
      (classSort resultOrder 0) (bindOrder resultOrder .individual))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual)
        (classSort resultOrder 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder resultOrder .individual)
          (classSort resultOrder 0))
        (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
          (classSort resultOrder 0))))
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual)
    (reducibility_scope_transport :
      (⊢ᵣ star_20_3_transportFormula universal equivalenceNegation
        equivalenceDisjunction leftNegation conjunctionDisjunction matrix x) →
      ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
        (star_12_1_formula reducibilityExistential universal
          equivalenceNegation equivalenceDisjunction matrix)
        (star_20_3_formula abstractionExistential universal
          equivalenceNegation equivalenceDisjunction leftNegation rightNegation
          outerNegation conjunctionDisjunction matrix x)) :
    Derivation (star_20_3_reading abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x).parsed := by
  have definitionUnfold := star_20_01_unfold abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix
    (star_20_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x)
  have line1 := star_20_1 abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction finalNegation finalDisjunction
    matrix (star_20_3_continuation equivalenceNegation
      equivalenceDisjunction matrix x)
  have line2 := star_20_02_unfold
    (.apparent (.zero : Var [classSort resultOrder 0]
      (classSort resultOrder 0))) x.weaken
  have line3 := star_10_43 universal equivalenceNegation
    equivalenceDisjunction leftNegation conjunctionDisjunction
    (star_20_3_predicateMatrix matrix) matrix.weakenReal x.weakenReal
  have line4 := reducibility_scope_transport line3
  have line5 := star_12_1 reducibilityExistential universal
    equivalenceNegation equivalenceDisjunction matrix
  have line6 := Derivation.star_9_12 reducibilityOuterNegation
    bridgeDisjunction line5 line4
  change ⊢ᵣ star_20_3_formula abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix x at line6 ⊢
  unfold star_20_1_reading at line1
  rw [star_20_1_left_unfold] at line1
  change ⊢ᵣ star_4_01 finalNegation finalDisjunction
    (star_20_3_formula abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x)
    (star_20_3_formula abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x) at line1
  unfold star_20_3_formula at line1 line6 ⊢
  rw [definitionUnfold] at line6 ⊢
  unfold star_20_3_continuation at line1 line6 ⊢
  rw [line2] at line1 line6 ⊢
  let target := Formula.sometimes abstractionExistential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      (equivalence equivalenceNegation equivalenceDisjunction
        (applyUnary (.apparent .zero) x.weaken)
        ((matrix.instantiate x).rename
          (emptyRenaming (target := [classSort resultOrder 0])))))
  change ⊢ᵣ target at line6 ⊢
  change ⊢ᵣ star_4_01 finalNegation finalDisjunction target target at line1
  have line7 : ⊢ᵣ implication finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target)
      (implication finalNegation finalDisjunction target
        (conjunction finalNegation finalDisjunction
          (star_4_01 finalNegation finalDisjunction target target) target)) :=
    star_3_2 finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target
  have line8 : ⊢ᵣ implication finalNegation finalDisjunction target
      (conjunction finalNegation finalDisjunction
        (star_4_01 finalNegation finalDisjunction target target) target) :=
    Derivation.star_9_12_same finalNegation finalDisjunction line1 line7
  have line9 : ⊢ᵣ conjunction finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target :=
    Derivation.star_9_12_same finalNegation finalDisjunction line6 line8
  exact Derivation.star_9_12_same finalNegation finalDisjunction line9
    (star_3_27 finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target)

/-- Audited catalogue reading of ✱20·6. -/
def star_20_6_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (body : Formula signature real [classSort resultOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : (∃α) . fα .≡ . ∼{(α) . ∼fα}"
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_20_071 existential body)
    (.neg existential.outerNegation
      (star_20_07 existential.universal
        (.neg existential.matrixNegation body))))

/-- ✱20·6, following PM's printed ✱4·2, ✱10·01, ✱20·07 chain.
`demonstration_provenance: follows-printed`. -/
theorem star_20_6
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (body : Formula signature real [classSort resultOrder 0] matrixOrder) :
    Derivation (star_20_6_reading existential equivalenceNegation
      equivalenceDisjunction body).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_20_071 existential body)
  have line2 : star_20_071 existential body =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation body)) :=
    star_10_01_unfold existential body
  have line3 := star_20_07_unfold existential.universal
    (.neg existential.matrixNegation body)
  exact Derivation.castAssertion
    (congrArg
      (star_4_01 equivalenceNegation equivalenceDisjunction
        (star_20_071 existential body))
      (Eq.trans line2
        (congrArg
          (fun formula => Formula.neg existential.outerNegation formula)
          line3).symm))
    line1

/-- Audited catalogue reading of ✱20·34.  The class variable is exactly the
predicative unary-function variable quantified in Leibniz identity ✱13·01. -/
def star_20_34_reading
    (vocabulary : IdentityVocabulary signature .individual order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (x y : Term signature real [] .individual) :
    ClaimReading signature real where
  printed := "⊢ : x = y .≡ : x ∈ α .⊃ₐ. y ∈ α"
  parsed := .assertion (star_4_01 equivalenceNegation
    equivalenceDisjunction
    (star_13_01 vocabulary x y)
    (star_20_07 vocabulary.universal
      (implication vocabulary.negation vocabulary.disjunction
        (star_20_02 (.apparent .zero) x.weaken)
        (star_20_02 (.apparent .zero) y.weaken))))

/-- ✱20·34.  PM prints no proof; unfolding ✱13·01, ✱20·07 and ✱20·02
gives the same object formula on both sides.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_20_34
    (vocabulary : IdentityVocabulary signature .individual order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (x y : Term signature real [] .individual) :
    Derivation (star_20_34_reading vocabulary equivalenceNegation
      equivalenceDisjunction x y).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_13_01 vocabulary x y)
  exact line1

/-- Audited catalogue reading of ✱20·61. -/
def star_20_61_reading
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (classSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (beta : Term signature real [] (classSort resultOrder 0)) :
    ClaimReading signature real where
  printed := "⊢ : (α) . fα .⊃ . fβ"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal body) (body.instantiate beta))

/-- ✱20·61, by the printed use of universal instantiation ✱10·1.
`demonstration_provenance: follows-printed`. -/
theorem star_20_61
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (classSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (beta : Term signature real [] (classSort resultOrder 0)) :
    Derivation
      (star_20_61_reading universal negation disjunction body beta).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction body beta
  exact line1

/-- Audited catalogue reading of the metalinguistic rule ✱20·62. -/
def star_20_62_reading
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "When fβ is true, whatever possible argument of the form ẑ(φ!z) β may be, then (α). fα is true."
  parsed := .assertion (.always universal body)

/-- ✱20·62, following the printed application of the rule ✱10·11.
The premise is legitimate because PM states ✱20·62 as a rule, not with `⊢`.
`demonstration_provenance: follows-printed`. -/
theorem star_20_62
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (classSort resultOrder 0 :: real)
          (classSort resultOrder 0)))))) :
    Derivation (star_20_62_reading universal body).parsed := by
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-- Audited catalogue reading of ✱20·63. -/
def star_20_63_reading
    (universal : signature.Universal (classSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (classSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [classSort resultOrder 0] 0) :
    ClaimReading signature real where
  printed := "⊢ : (α). p ∨ fα .⊃ : p .∨ . (α). fα"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body))
    (star_9_04 universal matrixDisjunction p body))

/-- ✱20·63 is the class-sorted instance of ✱9·25.  Its printed right
member is built with the eliminable definition ✱9·04, independently of the
explicitly universal left member.
`demonstration_provenance: follows-printed`. -/
theorem star_20_63
    (universal : signature.Universal (classSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (classSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [classSort resultOrder 0] 0) :
    Derivation (star_20_63_reading universal matrixDisjunction negation
      disjunction p body).parsed := by
  have line1 := star_9_23 universal negation disjunction
    (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body)
  unfold star_20_63_reading
  rw [star_9_04_unfold]
  exact line1

/-- Audited catalogue reading of ✱20·631. -/
def star_20_631_reading
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If \"fα\" is significant, then if β is of the same type as α, \"fβ\" is significant, and vice versa."
  parsed := .significance body

/-- ✱20·631, following PM's reduction to ✱10·121.
`demonstration_provenance: follows-printed`. -/
theorem star_20_631
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_631_reading body).parsed := by
  have line1 := Derivation.star_10_121 body
  exact line1

/-- Audited catalogue reading of ✱20·632. -/
def star_20_632_reading
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If, for some α, there is a proposition fα, then there is a function fα̂, and vice versa."
  parsed := .functionExistence body

/-- ✱20·632, following PM's reduction to ✱10·122.
`demonstration_provenance: follows-printed`. -/
theorem star_20_632
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_632_reading body).parsed := by
  have line1 := Derivation.star_10_122 body
  exact line1

/-- Audited catalogue reading of ✱20·633. -/
def star_20_633_reading
    (leftInner : signature.Universal (classSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (classSort rightOrder 0)
      (bindOrder matrixOrder (classSort leftOrder 0)))
    (rightInner : signature.Universal (classSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (classSort leftOrder 0)
      (bindOrder matrixOrder (classSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
        (classSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
          (classSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (classSort rightOrder 0))
          (classSort leftOrder 0))))
    (body : Formula signature real
      [classSort leftOrder 0, classSort rightOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "\"Whatever possible class α may be, f(α,β) is true whatever possible class β may be\" implies the corresponding statement with α and β interchanged except in \"f(α,β)\"."
  parsed := .assertion (star_11_07_formula leftInner rightOuter rightInner
    leftOuter negation disjunction body)

/-- ✱20·633, reconstructed as the class-sorted instance of ✱11·07.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_20_633
    (leftInner : signature.Universal (classSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (classSort rightOrder 0)
      (bindOrder matrixOrder (classSort leftOrder 0)))
    (rightInner : signature.Universal (classSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (classSort leftOrder 0)
      (bindOrder matrixOrder (classSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
        (classSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
          (classSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (classSort rightOrder 0))
          (classSort leftOrder 0))))
    (body : Formula signature real
      [classSort leftOrder 0, classSort rightOrder 0] matrixOrder) :
    Derivation (star_20_633_reading leftInner rightOuter rightInner leftOuter
      negation disjunction body).parsed := by
  have line1 := Derivation.star_11_07 leftInner rightOuter rightInner leftOuter
    negation disjunction body
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_20_61
#print axioms PM.RamifiedSyntax.star_20_62
#print axioms PM.RamifiedSyntax.star_20_63
#print axioms PM.RamifiedSyntax.star_20_631
#print axioms PM.RamifiedSyntax.star_20_632
#print axioms PM.RamifiedSyntax.star_20_633
#print axioms PM.RamifiedSyntax.star_20_1
#print axioms PM.RamifiedSyntax.star_20_15
#print axioms PM.RamifiedSyntax.star_20_3
#print axioms PM.RamifiedSyntax.star_20_6
#print axioms PM.RamifiedSyntax.star_20_34
#print axioms PM.RamifiedSyntax.star_20_04_unfold
#print axioms PM.RamifiedSyntax.star_20_05_unfold
#print axioms PM.RamifiedSyntax.star_20_06_unfold
#print axioms PM.RamifiedSyntax.star_20_07_unfold
#print axioms PM.RamifiedSyntax.star_20_071_unfold
#print axioms PM.RamifiedSyntax.star_20_081_unfold
