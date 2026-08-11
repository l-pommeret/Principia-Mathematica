namespace PM.DescriptionSyntax

/-! # Contextual descriptions (✱14)

This is the canonical syntax gate for the incomplete symbol introduced at
✱14·01.  A description is deliberately absent from `Term`.  Its bracket is a
constructor of `Formula`, and binds the candidate used by both the condition
and the continuation.  Consequently an occurrence of `(℩x)(φx)` cannot escape
its printed propositional scope as a denoting object.

`ObjectSort` remains a parameter: this file does not collapse PM's typical
ambiguity to one concrete individual type.  `order` is an explicit assigned
order, and every logical sign carries its meaning at that order.  Lean `Prop`
is used only below for metatheorems about these syntax trees, never as the
object language.

Source witness: first-edition volume I, leaf 203 / printed p. 181, SHA-256
`12a57b46d16f08df1de909a28f2cc91553861a1ea5d191922791e050fc0ebabc`;
the continuation of the definition is checked against leaf 204 / printed
p. 182, SHA-256
`23427375b6f708a53ed91a28fb43eed247d732ff4047ee7e88fd779e2a50ad28`.
-/

universe u

/-- Intrinsically typed de Bruijn variables. -/
inductive Var {ObjectSort : Type u} : List ObjectSort → ObjectSort → Type u where
  | zero : Var (sort :: context) sort
  | succ : Var context sort → Var (other :: context) sort

/-- The nonlogical and logical vocabulary at explicitly assigned orders. -/
structure Signature (ObjectSort : Type u) where
  Symbol : ObjectSort → Type u
  Predicate : List ObjectSort → Nat → Type u
  EqualityMeaning : ObjectSort → Nat → Type u
  NegationMeaning : Nat → Type u
  DisjunctionMeaning : Nat → Type u
  UniversalMeaning : ObjectSort → Nat → Type u
  ExistentialMeaning : ObjectSort → Nat → Type u

/-- Genuine object-language terms.  There is intentionally no description
constructor: descriptions are incomplete symbols, not names. -/
inductive Term {ObjectSort : Type u} (signature : Signature ObjectSort)
    (realContext apparentContext : List ObjectSort) : ObjectSort → Type u where
  | real : Var realContext sort → Term signature realContext apparentContext sort
  | apparent : Var apparentContext sort →
      Term signature realContext apparentContext sort
  | symbol : signature.Symbol sort →
      Term signature realContext apparentContext sort

/-- A typed argument vector for an atomic propositional function. -/
inductive Arguments {ObjectSort : Type u} (signature : Signature ObjectSort)
    (realContext apparentContext : List ObjectSort) : List ObjectSort → Type u where
  | nil : Arguments signature realContext apparentContext []
  | cons : Term signature realContext apparentContext sort →
      Arguments signature realContext apparentContext sorts →
      Arguments signature realContext apparentContext (sort :: sorts)

/-- Description-free formulae.  This is the codomain of ✱14·01 expansion.
The real context, apparent context, and assigned order are indices rather than
fixed parameters: binders change the apparent-context index intrinsically. -/
inductive CoreFormula {ObjectSort : Type u} (signature : Signature ObjectSort) :
    (realContext apparentContext : List ObjectSort) → Nat → Type u where
  | atom : signature.Predicate sorts order →
      Arguments signature realContext apparentContext sorts →
      CoreFormula signature realContext apparentContext order
  | equal : signature.EqualityMeaning sort order →
      Term signature realContext apparentContext sort →
      Term signature realContext apparentContext sort →
      CoreFormula signature realContext apparentContext order
  | neg : signature.NegationMeaning order →
      CoreFormula signature realContext apparentContext order →
      CoreFormula signature realContext apparentContext order
  | disj : signature.DisjunctionMeaning order →
      CoreFormula signature realContext apparentContext order →
      CoreFormula signature realContext apparentContext order →
      CoreFormula signature realContext apparentContext order
  | always : signature.UniversalMeaning sort order →
      CoreFormula signature realContext (sort :: apparentContext) order →
      CoreFormula signature realContext apparentContext order
  | sometimes : signature.ExistentialMeaning sort order →
      CoreFormula signature realContext (sort :: apparentContext) order →
      CoreFormula signature realContext apparentContext order

/-- The exact logical meanings needed by the contextual definition of one
description at one argument sort and assigned order.  Carrying this record is
local evidence, not a global axiom identifying logical signs across orders. -/
structure DescriptionVocabulary {ObjectSort : Type u} (signature : Signature ObjectSort)
    (sort : ObjectSort) (order : Nat) where
  equality : signature.EqualityMeaning sort order
  negation : signature.NegationMeaning order
  disjunction : signature.DisjunctionMeaning order
  universal : signature.UniversalMeaning sort order
  existential : signature.ExistentialMeaning sort order

/-- Formulae before incomplete symbols have been eliminated.  The
`descriptionScope` constructor is the object-syntactic citizen corresponding
to PM's printed bracket `[(℩x)(φx)]`.  Both children live under the same fresh,
typed candidate binder. -/
inductive Formula {ObjectSort : Type u} (signature : Signature ObjectSort) :
    (realContext apparentContext : List ObjectSort) → Nat → Type u where
  | atom : signature.Predicate sorts order →
      Arguments signature realContext apparentContext sorts →
      Formula signature realContext apparentContext order
  | equal : signature.EqualityMeaning sort order →
      Term signature realContext apparentContext sort →
      Term signature realContext apparentContext sort →
      Formula signature realContext apparentContext order
  | neg : signature.NegationMeaning order →
      Formula signature realContext apparentContext order →
      Formula signature realContext apparentContext order
  | disj : signature.DisjunctionMeaning order →
      Formula signature realContext apparentContext order →
      Formula signature realContext apparentContext order →
      Formula signature realContext apparentContext order
  | always : signature.UniversalMeaning sort order →
      Formula signature realContext (sort :: apparentContext) order →
      Formula signature realContext apparentContext order
  | sometimes : signature.ExistentialMeaning sort order →
      Formula signature realContext (sort :: apparentContext) order →
      Formula signature realContext apparentContext order
  | descriptionScope : DescriptionVocabulary signature sort order →
      (condition : Formula signature realContext (sort :: apparentContext) order) →
      (continuation : Formula signature realContext (sort :: apparentContext) order) →
      Formula signature realContext apparentContext order

abbrev Substitution {ObjectSort : Type u} (signature : Signature ObjectSort)
    (realContext source target : List ObjectSort) :=
  {sort : ObjectSort} → Var source sort → Term signature realContext target sort

def liftSubstitution (substitution : Substitution signature realContext source target) :
    Substitution signature realContext (sort :: source) (sort :: target)
  | _, .zero => .apparent .zero
  | _, .succ entry =>
      match substitution entry with
      | .real entry => .real entry
      | .apparent entry => .apparent (.succ entry)
      | .symbol (sort := _) payload => .symbol payload

def Term.substitute (substitution : Substitution signature realContext source target) :
    Term signature realContext source sort → Term signature realContext target sort
  | .real entry => .real entry
  | .apparent entry => substitution entry
  | .symbol (sort := _) payload => .symbol payload

def Arguments.substitute
    (substitution : Substitution signature realContext source target) :
    Arguments signature realContext source sorts →
      Arguments signature realContext target sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.substitute substitution) (arguments.substitute substitution)

def CoreFormula.substitute
    (substitution : Substitution signature realContext source target) :
    CoreFormula signature realContext source order →
      CoreFormula signature realContext target order
  | .atom predicate arguments => .atom predicate (arguments.substitute substitution)
  | .equal meaning left right =>
      .equal meaning (left.substitute substitution) (right.substitute substitution)
  | .neg meaning body => .neg meaning (body.substitute substitution)
  | .disj meaning left right =>
      .disj meaning (left.substitute substitution) (right.substitute substitution)
  | .always meaning body =>
      .always meaning (body.substitute (liftSubstitution substitution))
  | .sometimes meaning body =>
      .sometimes meaning (body.substitute (liftSubstitution substitution))

def Formula.substitute
    (substitution : Substitution signature realContext source target) :
    Formula signature realContext source order →
      Formula signature realContext target order
  | .atom predicate arguments => .atom predicate (arguments.substitute substitution)
  | .equal meaning left right =>
      .equal meaning (left.substitute substitution) (right.substitute substitution)
  | .neg meaning body => .neg meaning (body.substitute substitution)
  | .disj meaning left right =>
      .disj meaning (left.substitute substitution) (right.substitute substitution)
  | .always meaning body =>
      .always meaning (body.substitute (liftSubstitution substitution))
  | .sometimes meaning body =>
      .sometimes meaning (body.substitute (liftSubstitution substitution))
  | .descriptionScope vocabulary condition continuation =>
      .descriptionScope vocabulary
        (condition.substitute (liftSubstitution substitution))
        (continuation.substitute (liftSubstitution substitution))

/-- Shift every existing apparent entry across one fresh binder. -/
def weakeningSubstitution :
    Substitution signature realContext apparentContext (fresh :: apparentContext)
  | _, entry => .apparent (.succ entry)

def Formula.weaken
    (formula : Formula signature realContext apparentContext order) :
    Formula signature realContext (fresh :: apparentContext) order :=
  formula.substitute weakeningSubstitution

namespace CoreFormula

def imp (vocabulary : DescriptionVocabulary signature sort order)
    (left right : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  .disj vocabulary.disjunction (.neg vocabulary.negation left) right

def conj (vocabulary : DescriptionVocabulary signature sort order)
    (left right : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  .neg vocabulary.negation
    (.disj vocabulary.disjunction (.neg vocabulary.negation left)
      (.neg vocabulary.negation right))

def iff (vocabulary : DescriptionVocabulary signature sort order)
    (left right : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  conj vocabulary (imp vocabulary left right) (imp vocabulary right left)

/-- Substitute the fresh inner entry for the argument of a one-entry
matrix.  Tail variables cross both the retained candidate and the fresh
entry, so capture is impossible by construction. -/
def conditionAtFreshSubstitution :
    Substitution signature realContext (sort :: apparentContext)
      (sort :: sort :: apparentContext)
  | _, .zero => .apparent .zero
  | _, .succ entry => .apparent (.succ (.succ entry))

/-- The uniqueness matrix `(x) : φx ≡ x=b` in the candidate context.  There
is no extra `φb` conjunct: this preserves the printed ✱14·01 definiens rather
than replacing it by a merely equivalent modern formulation. -/
def uniquely (vocabulary : DescriptionVocabulary signature sort order)
    (condition : CoreFormula signature realContext (sort :: apparentContext) order) :
    CoreFormula signature realContext (sort :: apparentContext) order :=
  let conditionAtFresh := condition.substitute conditionAtFreshSubstitution
  let fresh : Term signature realContext (sort :: sort :: apparentContext) sort :=
    .apparent .zero
  let candidate : Term signature realContext (sort :: sort :: apparentContext) sort :=
    .apparent (.succ .zero)
  let equality := CoreFormula.equal vocabulary.equality fresh candidate
  .always vocabulary.universal (iff vocabulary conditionAtFresh equality)

end CoreFormula

namespace Formula

def imp (vocabulary : DescriptionVocabulary signature sort order)
    (left right : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  .disj vocabulary.disjunction (.neg vocabulary.negation left) right

/-- `[Desc] . ψ(Desc) . ⊃ . p`: only the antecedent is in the description
bracket. -/
def narrowDescriptionImplication
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext (sort :: apparentContext) order)
    (consequent : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  imp vocabulary (.descriptionScope vocabulary condition matrix) consequent

/-- `[Desc] : ψ(Desc) . ⊃ . p`: the implication itself is in the description
bracket.  Weakening moves `p` under the candidate binder without capture. -/
def wideDescriptionImplication
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext (sort :: apparentContext) order)
    (consequent : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope vocabulary condition
    (imp vocabulary matrix consequent.weaken)

/-- The narrow reading has implication, not the scope bracket, at its root. -/
theorem narrowDescriptionImplication_shape
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext (sort :: apparentContext) order)
    (consequent : Formula signature realContext apparentContext order) :
    narrowDescriptionImplication vocabulary condition matrix consequent =
      .disj vocabulary.disjunction
        (.neg vocabulary.negation
          (.descriptionScope vocabulary condition matrix)) consequent := rfl

/-- The wide reading has the description scope bracket at its root. -/
theorem wideDescriptionImplication_shape
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext (sort :: apparentContext) order)
    (consequent : Formula signature realContext apparentContext order) :
    wideDescriptionImplication vocabulary condition matrix consequent =
      .descriptionScope vocabulary condition
        (.disj vocabulary.disjunction (.neg vocabulary.negation matrix)
          consequent.weaken) := rfl

/-- ✱14·01, as a total capture-safe elimination into description-free syntax:
`[(℩x)(φx)]. ψ((℩x)(φx))` expands to
`(∃b) : (x) : φx ≡ x=b : ψb`.

Nested scopes are expanded recursively.  Neither the output type nor any
constructor of `Term` can contain a description. -/
def expand : Formula signature realContext apparentContext order →
    CoreFormula signature realContext apparentContext order
  | .atom predicate arguments => .atom predicate arguments
  | .equal meaning left right => .equal meaning left right
  | .neg meaning body => .neg meaning body.expand
  | .disj meaning left right => .disj meaning left.expand right.expand
  | .always meaning body => .always meaning body.expand
  | .sometimes meaning body => .sometimes meaning body.expand
  | .descriptionScope vocabulary condition continuation =>
      .sometimes vocabulary.existential
        (CoreFormula.conj vocabulary
          (CoreFormula.uniquely vocabulary condition.expand)
          continuation.expand)

/-- Structural β-law for the canonical ✱14·01 expansion. -/
theorem expand_descriptionScope
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition continuation :
      Formula signature realContext (sort :: apparentContext) order) :
    expand (.descriptionScope vocabulary condition continuation) =
      .sometimes vocabulary.existential
        (CoreFormula.conj vocabulary
          (CoreFormula.uniquely vocabulary condition.expand)
          continuation.expand) := rfl

end Formula

end PM.DescriptionSyntax
