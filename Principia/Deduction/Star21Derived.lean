import Principia.FirstEdition.Volume1.Star21Source
import Principia.Deduction.Star20Derived
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star11Derived
import Principia.Deduction.Star12Derived
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱21 -/

/-- ✱21·07: quantification over relations is quantification over
predicative two-place functions. -/
def star_21_07
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (relationSort resultOrder 0)) :=
  .always universal body

theorem star_21_07_unfold
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_21_07 universal body = .always universal body := rfl

/-- ✱21·071: existential relation quantification has the same predicative
two-place-function expansion as ✱21·07. -/
def star_21_071
    (existential : ExistentialVocabulary signature
      (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (relationSort resultOrder 0)) :=
  .sometimes existential body

theorem star_21_071_unfold
    (existential : ExistentialVocabulary signature
      (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_21_071 existential body = .sometimes existential body := rfl

/-- ✱21·02: application of a predicative binary relation function. -/
def star_21_02
    (relation : Term signature real apparent (relationSort resultOrder 0))
    (left right : Term signature real apparent .individual) :
    Formula signature real apparent resultOrder :=
  applyBinary relation left right

theorem star_21_02_unfold
    (relation : Term signature real apparent (relationSort resultOrder 0))
    (left right : Term signature real apparent .individual) :
    star_21_02 relation left right = applyBinary relation left right := rfl

/-! ## Remaining eliminable definitions of ✱21 -/

/-- ✱21·03: `Rel` is the contextual class abstraction whose displayed
matrix says that its relation argument is represented by a predicative binary
function.  The inner matrix is supplied at its exact ramified order. -/
def star_21_03
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort relationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder)
        (.function [relationSort relationOrder 0] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_21_03_unfold
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort relationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_21_03 existential universal equivalenceNegation
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

/-- Printed-to-AST reading of ✱21·03. -/
def star_21_03_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real [relationSort relationOrder 0]
      resultOrder)
    (continuation : Formula signature real
      [.function [relationSort relationOrder 0] resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "Rel = ẑR{(∃φ). R = ẑxẑyφ!(x,y)}  Df"
  parsed := .assertion
    (star_21_03 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  scopeReading := "Rel is eliminated contextually as the class of relations represented by predicative binary functions."

/-- ✱21·072: a description of a relation has contextual scope.  This is
the relation-sort instance of ✱14·01. -/
def star_21_072
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (condition : Formula signature real
      (relationSort relationOrder 0 :: apparent)
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (continuation : Formula signature real
      (relationSort relationOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (bindOrder identityBaseOrder
          (.function [relationSort relationOrder 0] identityBaseOrder
            identityExcess)) (relationSort relationOrder 0)) scopeOrder)
        (relationSort relationOrder 0)) :=
  star_14_01 existential universal identityVocabulary equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction condition continuation

theorem star_21_072_unfold
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (condition : Formula signature real
      (relationSort relationOrder 0 :: apparent)
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (continuation : Formula signature real
      (relationSort relationOrder 0 :: apparent) scopeOrder) :
    star_21_072 existential universal identityVocabulary equivalenceNegation
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

/-- Printed-to-AST reading of ✱21·072. -/
def star_21_072_reading
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder 0)
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) identityBaseOrder identityExcess)
    (equivalenceNegation : signature.Negation
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)) (relationSort relationOrder 0)) scopeOrder))
    (condition : Formula signature real [relationSort relationOrder 0]
      (bindOrder identityBaseOrder
        (.function [relationSort relationOrder 0] identityBaseOrder
          identityExcess)))
    (continuation : Formula signature real [relationSort relationOrder 0]
      scopeOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted "[(℩R)(φR)]. f(℩R)(φR) .=: (∃S) : φR .≡ᴿ. R = S : fS  Df"
  parsed := .assertion
    (star_21_072 existential universal identityVocabulary
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction condition continuation)
  scopeReading := "The relation description remains contextual and unfolds through the relation-sort instance of ✱14·01."

/-- ✱21·08: contextual abstraction of a two-place matrix whose arguments
are themselves relations. -/
def star_21_08
    (existential : ExistentialVocabulary signature
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0)
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (leftUniversal : signature.Universal (relationSort leftRelationOrder 0)
      resultOrder)
    (rightUniversal : signature.Universal (relationSort rightRelationOrder 0)
      (bindOrder resultOrder (relationSort leftRelationOrder 0)))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort leftRelationOrder 0 ::
        relationSort rightRelationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder
          (bindOrder resultOrder (relationSort leftRelationOrder 0))
          (relationSort rightRelationOrder 0)) scopeOrder)
        (.function [relationSort leftRelationOrder 0,
          relationSort rightRelationOrder 0] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      ((equivalence equivalenceNegation equivalenceDisjunction
        (matrix.rename (liftRenamingN
          [relationSort leftRelationOrder 0, relationSort rightRelationOrder 0]
          (fun v => .succ v)))
        (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
          (.apparent (.succ .zero)))).always₂ leftUniversal rightUniversal)
      continuation)

theorem star_21_08_unfold
    (existential : ExistentialVocabulary signature
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0)
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (leftUniversal : signature.Universal (relationSort leftRelationOrder 0)
      resultOrder)
    (rightUniversal : signature.Universal (relationSort rightRelationOrder 0)
      (bindOrder resultOrder (relationSort leftRelationOrder 0)))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort leftRelationOrder 0 ::
        relationSort rightRelationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_21_08 existential leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          ((equivalence equivalenceNegation equivalenceDisjunction
            (matrix.rename (liftRenamingN
              [relationSort leftRelationOrder 0,
                relationSort rightRelationOrder 0]
              (fun v => .succ v)))
            (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
              (.apparent (.succ .zero)))).always₂ leftUniversal rightUniversal)
          continuation) := rfl

/-- Printed-to-AST reading of ✱21·08. -/
def star_21_08_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0)
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (leftUniversal : signature.Universal (relationSort leftRelationOrder 0)
      resultOrder)
    (rightUniversal : signature.Universal (relationSort rightRelationOrder 0)
      (bindOrder resultOrder (relationSort leftRelationOrder 0)))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder
        (bindOrder resultOrder (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      [relationSort leftRelationOrder 0, relationSort rightRelationOrder 0]
      resultOrder)
    (continuation : Formula signature real
      [.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "f{ẑRẑSψ(R,S)} .=: (∃φ) : ψ(R,S) .≡₍R,S₎. φ!(R,S) : f{φ!(ẑR,ẑS)}  Df"
  parsed := .assertion
    (star_21_08 existential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix continuation)
  scopeReading := "Both apparent relation arguments are bound inside the contextual binary abstraction."

/-- ✱21·082: contextual unary abstraction over a relation argument. -/
def star_21_082
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort relationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder)
        (.function [relationSort relationOrder 0] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (matrix.rename (liftRenaming (fun v => .succ v)))
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))))
      continuation)

theorem star_21_082_unfold
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real
      (relationSort relationOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_21_082 existential universal equivalenceNegation
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

/-- Printed-to-AST reading of ✱21·082. -/
def star_21_082_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] resultOrder 0)
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (universal : signature.Universal (relationSort relationOrder 0)
      resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder (relationSort relationOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder (relationSort relationOrder 0)) scopeOrder))
    (matrix : Formula signature real [relationSort relationOrder 0]
      resultOrder)
    (continuation : Formula signature real
      [.function [relationSort relationOrder 0] resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "f{ẑR(ψR)} .=: (∃φ) : ψR .≡ᴿ. φ!R : f(φ!ẑR)  Df"
  parsed := .assertion
    (star_21_082 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  scopeReading := "The apparent relation variable has the full contextual abstraction as its scope."

/-- ✱21·083: membership of a relation in a predicative class of
relations is ordinary typed unary application. -/
def star_21_083
    (predicate : Term signature real apparent
      (.function [relationSort relationOrder 0] resultOrder 0))
    (relation : Term signature real apparent (relationSort relationOrder 0)) :
    Formula signature real apparent resultOrder :=
  applyUnary predicate relation

theorem star_21_083_unfold
    (predicate : Term signature real apparent
      (.function [relationSort relationOrder 0] resultOrder 0))
    (relation : Term signature real apparent (relationSort relationOrder 0)) :
    star_21_083 predicate relation = applyUnary predicate relation := rfl

/-- Printed-to-AST reading of ✱21·083. -/
def star_21_083_reading
    (predicate : Term signature real []
      (.function [relationSort relationOrder 0] resultOrder 0))
    (relation : Term signature real [] (relationSort relationOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "R ε φ!ẑR .= . φ!R  Df"
  parsed := .assertion (star_21_083 predicate relation)
  scopeReading := "Membership in the relation class reduces to application of its predicative unary function."

/-- Printed left member of ✱21·1, built through contextual relation
abstraction ✱21·01. -/
def star_21_1_left
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)) :=
  star_21_01 existential leftUniversal rightUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix continuation

/-- Printed right member of ✱21·1, built directly from the existential over
predicative binary relations. -/
def star_21_1_right
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)) :=
  Formula.sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      ((equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
          (.apparent (.succ .zero)))
        (matrix.rename (liftRenamingN [.individual, .individual]
          (fun v => .succ v)))).always₂ leftUniversal rightUniversal)
      continuation)

theorem star_21_1_left_unfold
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    star_21_1_left existential leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction matrix continuation =
      star_21_1_right existential leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction matrix continuation := rfl

/-- Audited catalogue reading of ✱21·1.  Its two printed members are built
independently; ✱21·01 proves that both unfold to the same tree. -/
def star_21_1_reading
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real
      [relationSort resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : f{ẑxẑyψ(x,y)} .≡ : (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{φ!(ẑu,ẑv)}"
  scopeReading := "The relation abstraction is eliminated contextually by ✱21·01."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_21_1_left existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_21_1_right existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation))

/-- ✱21·1, following PM's printed `[✱4·2.(✱21·01)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_21_1
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real
      [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_1_reading existential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction finalNegation finalDisjunction
      matrix continuation).parsed := by
  have line1 := star_4_2 finalNegation finalDisjunction
    (star_21_1_right existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  change Derivation (.assertion (star_4_01 finalNegation finalDisjunction
    (star_21_1_left existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_21_1_right existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)))
  rw [star_21_1_left_unfold]
  exact line1

/-! ## The eliminative theorem ✱21·3 -/

/-- The predicative relation matrix used by the two-argument specialization
of ✱10·43. -/
def star_21_3_relationMatrix
    (_matrix : Formula signature real [.individual, .individual] resultOrder) :
    Formula signature (relationSort resultOrder 0 :: real)
      [.individual, .individual] resultOrder :=
  star_21_02
    (.real (.zero : Var (relationSort resultOrder 0 :: real)
      (relationSort resultOrder 0)))
    (.apparent .zero) (.apparent (.succ .zero))

/-- The exact two-argument specialization used on PM's ✱10·43 line.  The
ramified API exposes this multiple generalization as ✱11·1. -/
def star_21_3_transportFormula
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    Formula signature (relationSort resultOrder 0 :: real) []
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder) :=
  star_11_1_formula leftUniversal rightUniversal outerNegation
    outerDisjunction
    (equivalence equivalenceNegation equivalenceDisjunction
      (star_21_3_relationMatrix matrix) matrix.weakenReal)
    x.weakenReal y.weakenReal

/-- The two-place instance of PM's ✱10·43 specialization.  The primitive
ramified representation of simultaneous two-variable specialization is
✱11·1, so this theorem is the exact binary instance used at ✱21·3. -/
theorem star_21_3_star_10_43
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    ⊢ᵣ star_21_3_transportFormula leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction outerNegation
      outerDisjunction matrix x y := by
  have line1 := star_11_1 leftUniversal rightUniversal outerNegation
    outerDisjunction
    (equivalence equivalenceNegation equivalenceDisjunction
      (star_21_3_relationMatrix matrix) matrix.weakenReal)
    x.weakenReal y.weakenReal
  exact line1

/-- The continuation obtained from the eliminable application definition
✱21·02. -/
def star_21_3_continuation
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    Formula signature real [relationSort resultOrder 0] resultOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (star_21_02 (.apparent .zero) x.weaken y.weaken)
    ((matrix.instantiate₂ x y).rename
      (emptyRenaming (target := [relationSort resultOrder 0])))

/-- Object formula of ✱21·3 after contextual expansion by ✱21·01. -/
def star_21_3_formula
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder)
        (relationSort resultOrder 0)) :=
  star_21_01 existential leftUniversal rightUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix
    (star_21_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x y)

/-- Audited catalogue reading of ✱21·3. -/
def star_21_3_reading
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱21·3. ⊢:xx̂ŷψ(x,y)y.≡.ψ(x,y) [*21·1·02.*10·43·35.*12·11]"
  scopeReading := "The incomplete relation abstraction has the scope of the displayed equivalence."
  parsed := .assertion (star_21_3_formula existential leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
    rightNegation outerNegation conjunctionDisjunction matrix x y)

/-- ✱21·3 modulo the same contextual reducibility-scope bridge as ✱20·3.

After unfolding, ✱12·11 starts with `.sometimes reducibilityExistential
(binaryReducibilityMatrix ...)`, whereas the required abstraction starts with
`.sometimes abstractionExistential (mixedConjunction ... (.always ...)
continuation)`.  The two existential vocabularies and bodies do not reduce to
one another, so ✱10·35 does not supply the bridge below.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_3
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort resultOrder 0)
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder resultOrder .individual) .individual)
        (relationSort resultOrder 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder resultOrder .individual) .individual)
          (relationSort resultOrder 0))
        (bindOrder
          (max (bindOrder (bindOrder resultOrder .individual) .individual)
            resultOrder)
          (relationSort resultOrder 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder)
        (relationSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder)
        (relationSort resultOrder 0)))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual)
    (reducibility_scope_transport :
      (⊢ᵣ star_21_3_transportFormula leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation
        conjunctionDisjunction matrix x y) →
      ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
        (star_12_11_formula reducibilityExistential leftUniversal
          rightUniversal equivalenceNegation equivalenceDisjunction matrix)
        (star_21_3_formula abstractionExistential leftUniversal
          rightUniversal equivalenceNegation equivalenceDisjunction
          leftNegation rightNegation outerNegation conjunctionDisjunction
          matrix x y)) :
    Derivation (star_21_3_reading abstractionExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
      rightNegation outerNegation conjunctionDisjunction matrix x y).parsed := by
  have definitionUnfold := star_21_01_unfold abstractionExistential leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
    rightNegation outerNegation conjunctionDisjunction matrix
    (star_21_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x y)
  have line1 := star_21_1 abstractionExistential leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
    rightNegation outerNegation conjunctionDisjunction finalNegation
    finalDisjunction matrix
    (star_21_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x y)
  have line2 := star_21_02_unfold
    (.apparent (.zero : Var [relationSort resultOrder 0]
      (relationSort resultOrder 0))) x.weaken y.weaken
  have line3 := star_21_3_star_10_43 leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation
    conjunctionDisjunction matrix x y
  have line4 := reducibility_scope_transport line3
  have line5 := star_12_11 reducibilityExistential leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction matrix
  have line6 := Derivation.star_9_12 reducibilityOuterNegation
    bridgeDisjunction line5 line4
  change ⊢ᵣ star_21_3_formula abstractionExistential leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
    rightNegation outerNegation conjunctionDisjunction matrix x y at line6 ⊢
  unfold star_21_1_reading at line1
  rw [star_21_1_left_unfold] at line1
  change ⊢ᵣ star_4_01 finalNegation finalDisjunction
    (star_21_3_formula abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x y)
    (star_21_3_formula abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x y) at line1
  unfold star_21_3_formula at line1 line6 ⊢
  rw [definitionUnfold] at line6 ⊢
  unfold star_21_3_continuation at line1 line6 ⊢
  rw [line2] at line1 line6 ⊢
  let target := Formula.sometimes abstractionExistential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      ((equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
          (.apparent (.succ .zero)))
        (matrix.rename (liftRenamingN [.individual, .individual]
          (fun v => .succ v)))).always₂ leftUniversal rightUniversal)
      (equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary (.apparent .zero) x.weaken y.weaken)
        ((matrix.instantiate₂ x y).rename
          (emptyRenaming (target := [relationSort resultOrder 0])))))
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

/-- Audited catalogue reading of ✱21·6. -/
def star_21_6_reading
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (body : Formula signature real [relationSort resultOrder 0] matrixOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃R). fR .≡ . ∼{(R). ∼fR}"
  scopeReading := "Both relation quantifiers bind the displayed matrix fR."
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_21_071 existential body)
    (.neg existential.outerNegation
      (star_21_07 existential.universal
        (.neg existential.matrixNegation body))))

/-- ✱21·6, following the printed instruction `[Proof as in ✱20·6]`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_6
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (body : Formula signature real [relationSort resultOrder 0] matrixOrder) :
    Derivation (star_21_6_reading existential equivalenceNegation
      equivalenceDisjunction body).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_21_071 existential body)
  have line2 : star_21_071 existential body =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation body)) :=
    star_10_01_unfold existential body
  have line3 := star_21_07_unfold existential.universal
    (.neg existential.matrixNegation body)
  exact Derivation.castAssertion
    (congrArg
      (star_4_01 equivalenceNegation equivalenceDisjunction
        (star_21_071 existential body))
      (Eq.trans line2
        (congrArg
          (fun formula => Formula.neg existential.outerNegation formula)
          line3).symm))
    line1

/-- Audited catalogue reading of ✱21·61. -/
def star_21_61_reading
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (relationSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (relation : Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (R). fR .⊃ . fS"
  scopeReading := "The universal relation quantifier is the antecedent of the implication."
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal body) (body.instantiate relation))

/-- ✱21·61, following the proof of ✱20·61 via ✱10·1.
`demonstration_provenance: follows-printed`. -/
theorem star_21_61
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (relationSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (relation : Term signature real [] (relationSort resultOrder 0)) :
    Derivation
      (star_21_61_reading universal negation disjunction body relation).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction body relation
  exact line1

/-- Audited catalogue reading of the metalinguistic rule ✱21·62. -/
def star_21_62_reading
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "When fR is true, whatever possible argument of the form ẑxẑyφ!(x,y) R may be, (R). fR is true."
  scopeReading := "The possible relation argument is bound in the asserted universal closure."
  parsed := .assertion (.always universal body)

/-- ✱21·62, following PM's reference to the proof of ✱20·62 via ✱10·11.
The premise is legitimate because PM states ✱21·62 as a rule, not with `⊢`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_62
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (relationSort resultOrder 0 :: real)
          (relationSort resultOrder 0)))))) :
    Derivation (star_21_62_reading universal body).parsed := by
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-- Audited catalogue reading of ✱21·63. -/
def star_21_63_reading
    (universal : signature.Universal (relationSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (relationSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [relationSort resultOrder 0] 0) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (R). p ∨ fR .⊃ : p .∨ . (R). fR"
  scopeReading := "The left quantifier covers p ∨ fR; the right one covers fR only."
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body))
    (star_9_04 universal matrixDisjunction p body))

/-- ✱21·63 is the relation-sorted instance of ✱9·25.  Its printed right
member is built with the eliminable definition ✱9·04, independently of the
explicitly universal left member.
`demonstration_provenance: follows-printed`. -/
theorem star_21_63
    (universal : signature.Universal (relationSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (relationSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [relationSort resultOrder 0] 0) :
    Derivation (star_21_63_reading universal matrixDisjunction negation
      disjunction p body).parsed := by
  have line1 := star_9_23 universal negation disjunction
    (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body)
  unfold star_21_63_reading
  rw [star_9_04_unfold]
  exact line1

/-- Audited catalogue reading of ✱21·631. -/
def star_21_631_reading
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "If \"fR\" is significant, then if S is of the same type as R, \"fS\" is significant, and vice versa."
  scopeReading := "Significance is attached to the typed one-relation matrix."
  parsed := .significance body

/-- ✱21·631, following PM's reference to the proof of ✱20·631.
`demonstration_provenance: follows-printed`. -/
theorem star_21_631
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_631_reading body).parsed := by
  have line1 := Derivation.star_10_121 body
  exact line1

/-- Audited catalogue reading of ✱21·632. -/
def star_21_632_reading
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "If, for some R, there is a proposition fR, then there is a function fR̂, and vice versa."
  scopeReading := "Function existence is attached to the typed one-relation matrix."
  parsed := .functionExistence body

/-- ✱21·632, following PM's reference to the proof of ✱20·632.
`demonstration_provenance: follows-printed`. -/
theorem star_21_632
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_632_reading body).parsed := by
  have line1 := Derivation.star_10_122 body
  exact line1

/-- Audited catalogue reading of ✱21·633. -/
def star_21_633_reading
    (leftInner : signature.Universal (relationSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (relationSort rightOrder 0)
      (bindOrder matrixOrder (relationSort leftOrder 0)))
    (rightInner : signature.Universal (relationSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (relationSort leftOrder 0)
      (bindOrder matrixOrder (relationSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
        (relationSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
          (relationSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (relationSort rightOrder 0))
          (relationSort leftOrder 0))))
    (body : Formula signature real
      [relationSort leftOrder 0, relationSort rightOrder 0] matrixOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "\"Whatever possible relation R may be, f(R,S) is true whatever possible relation S may be\" implies \"whatever possible relation S may be, f(R,S) is true whatever possible relation R may be.\""
  scopeReading := "The two universal relation binders are exchanged only outside the fixed matrix."
  parsed := .assertion (star_11_07_formula leftInner rightOuter rightInner
    leftOuter negation disjunction body)

/-- ✱21·633, following PM's reference to the proof of ✱20·633.
`demonstration_provenance: follows-printed`. -/
theorem star_21_633
    (leftInner : signature.Universal (relationSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (relationSort rightOrder 0)
      (bindOrder matrixOrder (relationSort leftOrder 0)))
    (rightInner : signature.Universal (relationSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (relationSort leftOrder 0)
      (bindOrder matrixOrder (relationSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
        (relationSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
          (relationSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (relationSort rightOrder 0))
          (relationSort leftOrder 0))))
    (body : Formula signature real
      [relationSort leftOrder 0, relationSort rightOrder 0] matrixOrder) :
    Derivation (star_21_633_reading leftInner rightOuter rightInner leftOuter
      negation disjunction body).parsed := by
  have line1 := Derivation.star_11_07 leftInner rightOuter rightInner leftOuter
    negation disjunction body
  exact line1

/-! ## Predicative representatives of functions of relations -/

/-- Audited catalogue reading of ✱21·7. -/
def star_21_7_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] order 0)
      (bindOrder order (relationSort relationOrder 0)))
    (universal : signature.Universal (relationSort relationOrder 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real [relationSort relationOrder 0] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : fR .≡ᴿ. g!R"
  scopeReading := "The existential predicative function binds the pointwise equivalence over R."
  parsed := .assertion
    (star_12_1_formula existential universal negation disjunction body)

/-- ✱21·7, following PM's reference to the proof of ✱20·7.  This is the
relation-sorted instance of the primitive reducibility proposition ✱12·1.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_7
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0] order 0)
      (bindOrder order (relationSort relationOrder 0)))
    (universal : signature.Universal (relationSort relationOrder 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real [relationSort relationOrder 0] order) :
    Derivation
      (star_21_7_reading existential universal negation disjunction body).parsed := by
  have line1 := star_20_7 (argumentSort := relationSort relationOrder 0)
    existential universal negation disjunction body
  exact line1

/-- Audited catalogue reading of ✱21·701. -/
def star_21_701_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, .individual] order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0)) .individual))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (individualUniversal : signature.Universal .individual
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, .individual] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : f(R,x) .≡₍R,x₎. g!(R,x)"
  scopeReading := "The existential predicative function binds the displayed (R,x)-equivalence."
  parsed := .assertion (star_12_11_formula existential relationUniversal
    individualUniversal negation disjunction body)

/-- ✱21·701, following PM's reference to the proof of ✱20·701.  It is the
`(R,x)` instance of ✱12·11.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_701
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, .individual] order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0)) .individual))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (individualUniversal : signature.Universal .individual
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, .individual] order) :
    Derivation (star_21_701_reading existential relationUniversal
      individualUniversal negation disjunction body).parsed := by
  have line1 := star_20_701 (argumentSort := relationSort relationOrder 0)
    existential relationUniversal individualUniversal negation disjunction body
  exact line1

/-- Audited catalogue reading of ✱21·702.  The arbitrary matrix denotes
`f(x,R)` while its apparent context remains in PM's displayed `(R,x)` order. -/
def star_21_702_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, .individual] order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0)) .individual))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (individualUniversal : signature.Universal .individual
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, .individual] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : f(x,R) .≡₍R,x₎. g!(R,x)"
  scopeReading := "The matrix reads f(x,R), while its typed binders occur in the displayed (R,x) order."
  parsed := .assertion (star_12_11_formula existential relationUniversal
    individualUniversal negation disjunction body)

/-- ✱21·702, following PM's reference to the proof of ✱20·702.  It is the
reordered-matrix instance of ✱12·11.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_702
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, .individual] order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0)) .individual))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (individualUniversal : signature.Universal .individual
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, .individual] order) :
    Derivation (star_21_702_reading existential relationUniversal
      individualUniversal negation disjunction body).parsed := by
  have line1 := star_20_702 (argumentSort := relationSort relationOrder 0)
    existential relationUniversal individualUniversal negation disjunction body
  exact line1

/-- Audited catalogue reading of ✱21·703. -/
def star_21_703_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] order 0)
      (bindOrder (bindOrder order (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)))
    (leftUniversal : signature.Universal
      (relationSort leftRelationOrder 0) order)
    (rightUniversal : signature.Universal (relationSort rightRelationOrder 0)
      (bindOrder order (relationSort leftRelationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort leftRelationOrder 0, relationSort rightRelationOrder 0]
      order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : f(R,S) .≡₍R,S₎. g!(R,S)"
  scopeReading := "The existential predicative function binds the displayed (R,S)-equivalence."
  parsed := .assertion (star_12_11_formula existential leftUniversal
    rightUniversal negation disjunction body)

/-- ✱21·703, following PM's reference to the proof of ✱20·703.  It is the
two-relation instance of ✱12·11.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_703
    (existential : ExistentialVocabulary signature
      (.function [relationSort leftRelationOrder 0,
        relationSort rightRelationOrder 0] order 0)
      (bindOrder (bindOrder order (relationSort leftRelationOrder 0))
        (relationSort rightRelationOrder 0)))
    (leftUniversal : signature.Universal
      (relationSort leftRelationOrder 0) order)
    (rightUniversal : signature.Universal (relationSort rightRelationOrder 0)
      (bindOrder order (relationSort leftRelationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort leftRelationOrder 0, relationSort rightRelationOrder 0]
      order) :
    Derivation (star_21_703_reading existential leftUniversal rightUniversal
      negation disjunction body).parsed := by
  have line1 := star_20_703
    (leftSort := relationSort leftRelationOrder 0)
    (rightSort := relationSort rightRelationOrder 0)
    existential leftUniversal rightUniversal negation disjunction body
  exact line1

/-- Audited catalogue reading of ✱21·704. -/
def star_21_704_reading
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, classSort classOrder 0]
        order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0))
        (classSort classOrder 0)))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (classUniversal : signature.Universal (classSort classOrder 0)
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, classSort classOrder 0] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : f(R,α) .≡₍R,α₎. g!(R,α)"
  scopeReading := "The existential predicative function binds the displayed mixed relation/class equivalence."
  parsed := .assertion (star_12_11_formula existential relationUniversal
    classUniversal negation disjunction body)

/-- ✱21·704, following PM's reference to the proof of ✱20·703.  It is the
mixed relation/class instance of ✱12·11.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_704
    (existential : ExistentialVocabulary signature
      (.function [relationSort relationOrder 0, classSort classOrder 0]
        order 0)
      (bindOrder (bindOrder order (relationSort relationOrder 0))
        (classSort classOrder 0)))
    (relationUniversal : signature.Universal
      (relationSort relationOrder 0) order)
    (classUniversal : signature.Universal (classSort classOrder 0)
      (bindOrder order (relationSort relationOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [relationSort relationOrder 0, classSort classOrder 0] order) :
    Derivation (star_21_704_reading existential relationUniversal
      classUniversal negation disjunction body).parsed := by
  have line1 := star_20_703
    (leftSort := relationSort relationOrder 0)
    (rightSort := classSort classOrder 0)
    existential relationUniversal classUniversal negation disjunction body
  exact line1

/-- Audited catalogue reading of ✱21·705. -/
def star_21_705_reading
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0, relationSort relationOrder 0]
        order 0)
      (bindOrder (bindOrder order (classSort classOrder 0))
        (relationSort relationOrder 0)))
    (classUniversal : signature.Universal (classSort classOrder 0) order)
    (relationUniversal : signature.Universal (relationSort relationOrder 0)
      (bindOrder order (classSort classOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [classSort classOrder 0, relationSort relationOrder 0] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : (∃g) : f(α,R) .≡₍α,R₎. g!(α,R)"
  scopeReading := "The existential predicative function binds the displayed mixed class/relation equivalence."
  parsed := .assertion (star_12_11_formula existential classUniversal
    relationUniversal negation disjunction body)

/-- ✱21·705, following PM's reference to the proof of ✱20·703.  It is the
mixed class/relation instance of ✱12·11.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_705
    (existential : ExistentialVocabulary signature
      (.function [classSort classOrder 0, relationSort relationOrder 0]
        order 0)
      (bindOrder (bindOrder order (classSort classOrder 0))
        (relationSort relationOrder 0)))
    (classUniversal : signature.Universal (classSort classOrder 0) order)
    (relationUniversal : signature.Universal (relationSort relationOrder 0)
      (bindOrder order (classSort classOrder 0)))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (body : Formula signature real
      [classSort classOrder 0, relationSort relationOrder 0] order) :
    Derivation (star_21_705_reading existential classUniversal
      relationUniversal negation disjunction body).parsed := by
  have line1 := star_20_703
    (leftSort := classSort classOrder 0)
    (rightSort := relationSort relationOrder 0)
    existential classUniversal relationUniversal negation disjunction body
  exact line1

/-- Printed left member of ✱21·71, built as relation identity. -/
def star_21_71_left
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) order 0)
    (left right : Term signature real [] (relationSort relationOrder 0)) :=
  star_13_01 identityVocabulary left right

/-- Printed right member of ✱21·71, built independently as the quantified
Leibniz implication over predicative functions of relations. -/
def star_21_71_right
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) order 0)
    (left right : Term signature real [] (relationSort relationOrder 0)) :
    Formula signature real []
      (bindOrder order
        (.function [relationSort relationOrder 0] order 0)) :=
  .always identityVocabulary.universal
    (implication identityVocabulary.negation identityVocabulary.disjunction
      (applyUnary (.apparent .zero) left.weaken)
      (applyUnary (.apparent .zero) right.weaken))

theorem star_21_71_left_unfold
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) order 0)
    (left right : Term signature real [] (relationSort relationOrder 0)) :
    star_21_71_left identityVocabulary left right =
      star_21_71_right identityVocabulary left right := rfl

/-- Audited catalogue reading of ✱21·71. -/
def star_21_71_reading
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order
        (.function [relationSort relationOrder 0] order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order
        (.function [relationSort relationOrder 0] order 0)))
    (left right : Term signature real [] (relationSort relationOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : R = S .≡ : g!R .⊃₍g₎. g!S"
  scopeReading := "The predicate-function quantifier in Leibniz identity covers the displayed implication."
  parsed := .assertion (star_4_01 equivalenceNegation
    equivalenceDisjunction
    (star_21_71_left identityVocabulary left right)
    (star_21_71_right identityVocabulary left right))

/-- ✱21·71, following PM's reference to the proof of ✱20·71.  Unfolding
Leibniz identity ✱13·01 makes the displayed equivalence reflexive.
`demonstration_provenance: follows-printed`. -/
theorem star_21_71
    (identityVocabulary : IdentityVocabulary signature
      (relationSort relationOrder 0) order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order
        (.function [relationSort relationOrder 0] order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order
        (.function [relationSort relationOrder 0] order 0)))
    (left right : Term signature real [] (relationSort relationOrder 0)) :
    Derivation (star_21_71_reading identityVocabulary equivalenceNegation
      equivalenceDisjunction left right).parsed := by
  have line1 := star_20_71 (argumentSort := relationSort relationOrder 0)
    identityVocabulary equivalenceNegation equivalenceDisjunction left right
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_21_61
#print axioms PM.RamifiedSyntax.star_21_62
#print axioms PM.RamifiedSyntax.star_21_63
#print axioms PM.RamifiedSyntax.star_21_631
#print axioms PM.RamifiedSyntax.star_21_632
#print axioms PM.RamifiedSyntax.star_21_633
#print axioms PM.RamifiedSyntax.star_21_7
#print axioms PM.RamifiedSyntax.star_21_701
#print axioms PM.RamifiedSyntax.star_21_702
#print axioms PM.RamifiedSyntax.star_21_703
#print axioms PM.RamifiedSyntax.star_21_704
#print axioms PM.RamifiedSyntax.star_21_705
#print axioms PM.RamifiedSyntax.star_21_71
#print axioms PM.RamifiedSyntax.star_21_1
#print axioms PM.RamifiedSyntax.star_21_3
#print axioms PM.RamifiedSyntax.star_21_3_star_10_43
#print axioms PM.RamifiedSyntax.star_21_6
#print axioms PM.RamifiedSyntax.star_21_02_unfold
#print axioms PM.RamifiedSyntax.star_21_07_unfold
#print axioms PM.RamifiedSyntax.star_21_071_unfold
