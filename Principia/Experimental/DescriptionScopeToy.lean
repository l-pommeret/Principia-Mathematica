namespace PM.Experimental.DescriptionScopeToy

/-! # Incomplete symbols and description scope: experimental gate

This isolated experiment tests the architectural constraint imposed by the
first-edition Introduction, Chapter III (pp. 69–75), and by the now-collated
opening of ✱14.  The canonical scan evidence is:

* whole volume DjVu, SHA-256
  `52fd0ba446ab2dc97f08d6d4b16d67196edb6d991b0a0445e1ee4dbb57fa2eab`;
* leaf 203 / printed p. 181, SHA-256
  `12a57b46d16f08df1de909a28f2cc91553861a1ea5d191922791e050fc0ebabc`;
* leaf 204 / printed p. 182, SHA-256
  `23427375b6f708a53ed91a28fb43eed247d732ff4047ee7e88fd779e2a50ad28`.

The scan agrees with Project Gutenberg 78050 (source SHA-256
`f9e000e6e66bcd865d03ad41bbf7cbc74618678eceb6af0fb113c3df51e0200a`);
the corresponding Wikisource pages are redlinks and supply no textual
witness.  In PM a description is not a name: only its use in a propositional
context is defined.  Accordingly there is deliberately no
`DescriptionTerm` constructor here.  `descriptionScope` takes both the
descriptive condition and the continuation in which its unique witness is
used.

The prototype uses a two-object domain only to give the scope distinction a
small, executable semantics.  It is not offered as the eventual semantics of
PM individuals.  The continuation representation is intrinsically
capture-safe: its object is bound by the Lean function space and cannot escape
as a term of the object language.
-/

/-- A tiny object domain used only for the separating countermodel. -/
inductive Object where
  | left
  | right
  deriving DecidableEq

/-- Core propositions left after every incomplete description has been
expanded away. -/
inductive CoreFormula where
  | truth : Bool → CoreFormula
  | neg : CoreFormula → CoreFormula
  | conj : CoreFormula → CoreFormula → CoreFormula
  | disj : CoreFormula → CoreFormula → CoreFormula

namespace CoreFormula

def eval : CoreFormula → Bool
  | .truth value => value
  | .neg body => !body.eval
  | .conj left right => left.eval && right.eval
  | .disj left right => left.eval || right.eval

def iff (left right : CoreFormula) : CoreFormula :=
  .conj (.disj (.neg left) right) (.disj (.neg right) left)

def imp (left right : CoreFormula) : CoreFormula :=
  .disj (.neg left) right

end CoreFormula

/-- Propositions before contextual definitions have been expanded.

There is no description-valued case.  A description can occur only through
`descriptionScope`, paired immediately with the propositional continuation
that consumes its witness.  Later incomplete symbols for classes and
relational descriptions can reuse this same contextual interface rather than
being promoted to object-language terms. -/
inductive Formula where
  | truth : Bool → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | descriptionScope :
      (condition : Object → Formula) →
      (continuation : Object → Formula) → Formula

namespace Formula

private def objectEq : Object → Object → CoreFormula
  | .left, .left => .truth true
  | .right, .right => .truth true
  | _, _ => .truth false

/-- `condition` holds of exactly `candidate`, written without introducing a
description-denoting term. -/
private def uniquely (condition : Object → CoreFormula)
    (candidate : Object) : CoreFormula :=
  .conj (condition candidate)
    (.conj
      (CoreFormula.iff (condition .left) (objectEq .left candidate))
      (CoreFormula.iff (condition .right) (objectEq .right candidate)))

/-- Capture-safe contextual expansion of the description definition in use:
`[(℩x)(φx)]. f((℩x)(φx))` becomes
`(∃c) : φx ≡ₓ x = c : fc`.

The two disjuncts are the finite-domain expansion of the existential.  No
description survives in the resulting core formula. -/
def expand : Formula → CoreFormula
  | .truth value => .truth value
  | .neg body => .neg body.expand
  | .conj left right => .conj left.expand right.expand
  | .disj left right => .disj left.expand right.expand
  | .imp left right => CoreFormula.imp left.expand right.expand
  | .descriptionScope condition continuation =>
      .disj
        (.conj (uniquely (fun x => (condition x).expand) .left)
          (continuation .left).expand)
        (.conj (uniquely (fun x => (condition x).expand) .right)
          (continuation .right).expand)

def eval (formula : Formula) : Bool := formula.expand.eval

/-- The deliberately non-denoting description in the countermodel. -/
def nonDenoting : Object → Formula := fun _ => .truth false

/-- An arbitrary matrix; its value is immaterial when the description fails
to denote, but making it nonconstant ensures the continuation is genuinely
fed the contextual witness. -/
def matrix : Object → Formula
  | .left => .truth true
  | .right => .truth false

/-- `∼{[(℩x)(φx)]. ψ((℩x)(φx))}`: negation lies outside the description's
scope. -/
def negOutsideDescription : Formula :=
  .neg (.descriptionScope nonDenoting matrix)

/-- `[(℩x)(φx)]. ∼ψ((℩x)(φx))`: negation lies inside the continuation and
therefore inside the description's scope. -/
def negInsideDescription : Formula :=
  .descriptionScope nonDenoting (fun x => .neg (matrix x))

/-- The wide-scope negation is true when the description does not denote. -/
theorem negOutsideDescription_isTrue :
    negOutsideDescription.eval = true := rfl

/-- The description-scoped negation is false when the description does not
denote. -/
theorem negInsideDescription_isFalse :
    negInsideDescription.eval = false := rfl

/-- This is semantic separation, not merely inequality of two syntax trees. -/
theorem scopeReadings_haveDifferentTruthValues :
    negOutsideDescription.eval ≠ negInsideDescription.eval := by
  decide

/-!
Printed p. 181 gives the canonical implication pair (letters normalized only
to the names used by this toy):

* narrow description scope: `[Desc] . ψ(Desc) . ⊃ . p`, expanded as
  `((∃b) : uniqueφ(b) : ψ(b)) ⊃ p`;
* wide description scope: `[Desc] : ψ(Desc) . ⊃ . p`, expanded as
  `(∃b) : uniqueφ(b) : (ψ(b) ⊃ p)`.

The next two definitions preserve those contextual shapes exactly.  The
countermodel chooses false `p`; when `φ` has no unique witness, the first
implication has a false antecedent and is true, whereas the second existential
description expansion is false.
-/

/-- `[Desc] . ψ(Desc) . ⊃ . p`: description scope is only the antecedent. -/
def narrowDescriptionImplication : Formula :=
  .imp (.descriptionScope nonDenoting matrix) (.truth false)

/-- `[Desc] : ψ(Desc) . ⊃ . p`: description scope includes the implication. -/
def wideDescriptionImplication : Formula :=
  .descriptionScope nonDenoting (fun x => .imp (matrix x) (.truth false))

theorem narrowDescriptionImplication_isTrue :
    narrowDescriptionImplication.eval = true := rfl

theorem wideDescriptionImplication_isFalse :
    wideDescriptionImplication.eval = false := rfl

/-- Semantic separation of the exact p. 181 implication readings. -/
theorem implicationScopeReadings_haveDifferentTruthValues :
    narrowDescriptionImplication.eval ≠ wideDescriptionImplication.eval := by
  decide

end Formula

end PM.Experimental.DescriptionScopeToy
