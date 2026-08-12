/-!
# PM I, ✱20·07–✱20·081

Exact reductional definitions for class variables.  Classes are represented
extensionally by their membership predicates; this module adds no class
object axiom, reducibility principle, or choice operation.
-/

namespace PM.Architecture.Star20Q317Definitions

abbrev Class (Object : Sort u) := Object → Prop

def ExtensionallyEqual (alpha beta : Class Object) : Prop :=
  ∀ x, alpha x ↔ beta x

/-- ✱20·07: universal class quantification reduces to universal
quantification over predicative characteristic functions. -/
def UniversalClass (f : Class Object → Prop) : Prop :=
  ∀ phi : Object → Prop, f phi

theorem star_20_07 (f : Class Object → Prop) :
    UniversalClass f = (∀ phi : Object → Prop, f phi) := rfl

/-- ✱20·071: existential class quantification has the corresponding
predicative-function reduction. -/
def ExistentialClass (f : Class Object → Prop) : Prop :=
  ∃ phi : Object → Prop, f phi

theorem star_20_071 (f : Class Object → Prop) :
    ExistentialClass f = (∃ phi : Object → Prop, f phi) := rfl

/-- Contextual application of the class description `(iα)(φα)`. -/
def ClassDescriptionScope
    (phi : Class Object → Prop) (f : Class Object → Prop) : Prop :=
  ∃ gamma, (∀ alpha, phi alpha ↔ alpha = gamma) ∧ f gamma

/-- ✱20·072: exact contextual expansion of a class description. -/
theorem star_20_072
    (phi : Class Object → Prop) (f : Class Object → Prop) :
    ClassDescriptionScope phi f =
      (∃ gamma, (∀ alpha, phi alpha ↔ alpha = gamma) ∧ f gamma) := rfl

/-- Application to a possibly non-predicative class function, reduced to an
extensionally equal predicative representative as in ✱20·08. -/
def ClassFunctionApplication
    (psi : Class Object → Prop) (f : (Class Object → Prop) → Prop) : Prop :=
  ∃ phi : Class Object → Prop, (∀ alpha, psi alpha ↔ phi alpha) ∧ f phi

theorem star_20_08
    (psi : Class Object → Prop) (f : (Class Object → Prop) → Prop) :
    ClassFunctionApplication psi f =
      (∃ phi : Class Object → Prop,
        (∀ alpha, psi alpha ↔ phi alpha) ∧ f phi) := rfl

/-- ✱20·081: membership in the class determined by `psi` reduces to
application of its characteristic function. -/
def Membership (alpha : Object) (psi : Class Object) : Prop := psi alpha

theorem star_20_081 (alpha : Object) (psi : Class Object) :
    Membership alpha psi = psi alpha := rfl

end PM.Architecture.Star20Q317Definitions
