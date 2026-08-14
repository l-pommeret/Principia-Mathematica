namespace PM.Architecture.Star23OpeningDerivation

/-! Object language for the opening of PM I ✱23.

`RelationTerm` and `RelationFormula` are syntax, not interpreted Lean
relations. `Derivation` is the primary PM judgment. No semantic `Prop` theorem
is used as a substitute for the printed assertions.
-/

mutual
  inductive RelationTerm where
    | relVar : String → RelationTerm
    | intersection : RelationTerm → RelationTerm → RelationTerm
    | union : RelationTerm → RelationTerm → RelationTerm
    | complement : RelationTerm → RelationTerm
    | difference : RelationTerm → RelationTerm → RelationTerm
    | abstraction : RelationFormula → RelationTerm
    deriving DecidableEq, Repr

  inductive RelationFormula where
    | applies : RelationTerm → RelationFormula
    | included : RelationTerm → RelationTerm → RelationFormula
    | equal : RelationTerm → RelationTerm → RelationFormula
    | neg : RelationFormula → RelationFormula
    | conj : RelationFormula → RelationFormula → RelationFormula
    | disj : RelationFormula → RelationFormula → RelationFormula
    | imp : RelationFormula → RelationFormula → RelationFormula
    | iff : RelationFormula → RelationFormula → RelationFormula
    | forallPair : RelationFormula → RelationFormula
    deriving DecidableEq, Repr
end

namespace RelationTerm

abbrev R := relVar "R"
abbrev S := relVar "S"

end RelationTerm

namespace RelationFormula

def inclusionExpansion (R S : RelationTerm) : RelationFormula :=
  forallPair (imp (applies R) (applies S))

def intersectionExpansion (R S : RelationTerm) : RelationTerm :=
  .abstraction (.conj (.applies R) (.applies S))

def unionExpansion (R S : RelationTerm) : RelationTerm :=
  .abstraction (.disj (.applies R) (.applies S))

def complementExpansion (R : RelationTerm) : RelationTerm :=
  .abstraction (.neg (.applies R))

def differenceExpansion (R S : RelationTerm) : RelationTerm :=
  .intersection R (.complement S)

def differencePointwiseExpansion (R S : RelationTerm) : RelationTerm :=
  .abstraction (.conj (.applies R) (.neg (.applies S)))

end RelationFormula

/-- Kernel judgment for the five opening assertions of ✱23. Each constructor
is the audited use of the adjacent printed definition, not a semantic axiom
about Lean relations. -/
inductive Derivation : RelationFormula → Prop where
  | star_23_01 (R S : RelationTerm) :
      Derivation (.iff (.included R S) (.inclusionExpansion R S))
  | star_23_02 (R S : RelationTerm) :
      Derivation (.equal (.intersection R S)
        (RelationFormula.intersectionExpansion R S))
  | star_23_03 (R S : RelationTerm) :
      Derivation (.equal (.union R S) (RelationFormula.unionExpansion R S))
  | star_23_04 (R : RelationTerm) :
      Derivation (.equal (.complement R)
        (RelationFormula.complementExpansion R))
  | star_23_05 (R S : RelationTerm) :
      Derivation (.equal (.difference R S)
        (RelationFormula.differenceExpansion R S))

notation:45 "⊢ᵣ " p => Derivation p

open RelationTerm RelationFormula

/-- PM I ✱23·1, object-syntactic assertion derived by ✱23·01. -/
theorem star_23_1 : ⊢ᵣ (.iff (.included R S) (.inclusionExpansion R S)) :=
  .star_23_01 R S

/-- PM I ✱23·2, object-syntactic assertion derived by ✱23·02. -/
theorem star_23_2 : ⊢ᵣ (.equal (.intersection R S)
    (RelationFormula.intersectionExpansion R S)) :=
  .star_23_02 R S

/-- PM I ✱23·3, object-syntactic assertion derived by ✱23·03. -/
theorem star_23_3 : ⊢ᵣ (.equal (.union R S)
    (RelationFormula.unionExpansion R S)) :=
  .star_23_03 R S

/-- PM I ✱23·31, object-syntactic assertion derived by ✱23·04. -/
theorem star_23_31 : ⊢ᵣ (.equal (.complement R)
    (RelationFormula.complementExpansion R)) :=
  .star_23_04 R

/-- Exact object-syntactic target printed at PM I ✱23·32.  A derivation of
this target still requires equality transport through ✱23·05, ·02 and ·04;
the narrow opening judgement deliberately does not pretend that ·05 alone is
that proof. -/
def star_23_32_target : RelationFormula :=
  .equal (.difference R S) (RelationFormula.differencePointwiseExpansion R S)

end PM.Architecture.Star23OpeningDerivation
