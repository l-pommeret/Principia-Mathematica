import Principia.Syntax.Description
import Principia.Syntax.Ordered

namespace PM.Experimental.UnifiedSyntaxEnvelope

/-!
# Indexed unified syntax envelope (experimental)

This file is syntax only.  It deliberately defines neither an assertion
judgement nor a derivation rule.  The envelope is a GADT whose index retains
the source family and every index that source family exposes; it is therefore
not a coercion between `Elementary`, `OrderedFormula`, and
`DescriptionSyntax.Formula`.

The planned unified judgement core may use this envelope only after separate
conservativity proofs have been supplied.  In particular, the injections here
do not turn an `Elementary` derivation into an `OrderedAssertion`, nor do they
provide any judgement for description syntax.
-/

open PM.DescriptionSyntax

universe u

/-- The index records the source syntax family before its formula is wrapped.

`ObjectSort` is retained even for the elementary and ordered cases so an
envelope never erases the universe parameter needed by the description case.
-/
inductive FamilyTag (ObjectSort : Type u) where
  | elementary (realContext : PM.RealContext)
  | ordered (realContext : PM.RealContext) (order : Nat)
  | description (signature : Signature ObjectSort) (realContext : List ObjectSort)
      (apparentContext : List ObjectSort) (order : Nat)

/-- A formula tagged with its original syntax family and all of that family's
indices.  This is an indexed envelope, not a common object-language grammar.
-/
inductive Envelope {ObjectSort : Type u} : FamilyTag ObjectSort → Type (u + 1) where
  | elementary {realContext : PM.RealContext} :
      PM.Elementary realContext → Envelope (.elementary realContext)
  | ordered {realContext : PM.RealContext} {order : Nat} :
      PM.OrderedFormula realContext order → Envelope (.ordered realContext order)
  | description {signature : Signature ObjectSort} {realContext apparentContext : List ObjectSort}
      {order : Nat} :
      Formula signature realContext apparentContext order →
        Envelope (.description signature realContext apparentContext order)

/-! ## Family injections and structural retractions -/

def injectElementary (formula : PM.Elementary realContext) :
    Envelope (ObjectSort := ObjectSort) (.elementary realContext) :=
  .elementary formula

def retractElementary : Envelope (ObjectSort := ObjectSort) (.elementary realContext) →
    PM.Elementary realContext
  | .elementary formula => formula

@[simp] theorem retract_injectElementary (formula : PM.Elementary realContext) :
    retractElementary (injectElementary (ObjectSort := ObjectSort) formula) = formula := rfl

theorem injectElementary_injective (ObjectSort : Type u) {realContext : PM.RealContext} :
    Function.Injective (injectElementary (ObjectSort := ObjectSort) (realContext := realContext)) := by
  intro left right equality
  cases equality
  rfl

def injectOrdered (formula : PM.OrderedFormula realContext order) :
    Envelope (ObjectSort := ObjectSort) (.ordered realContext order) :=
  .ordered formula

def retractOrdered : Envelope (ObjectSort := ObjectSort) (.ordered realContext order) →
    PM.OrderedFormula realContext order
  | .ordered formula => formula

@[simp] theorem retract_injectOrdered (formula : PM.OrderedFormula realContext order) :
    retractOrdered (injectOrdered (ObjectSort := ObjectSort) formula) = formula := rfl

theorem injectOrdered_injective (ObjectSort : Type u) {realContext : PM.RealContext} {order : Nat} :
    Function.Injective (injectOrdered (ObjectSort := ObjectSort) (realContext := realContext) (order := order)) := by
  intro left right equality
  cases equality
  rfl

/-- The only currently audited cross-family retraction is the existing
order-zero `OrderedFormula` eraser.  It stays partial: a first- or
second-order formula is never treated as elementary syntax. -/
def retractOrderedElementary? :
    Envelope (ObjectSort := ObjectSort) (.ordered realContext order) →
      Option (PM.Elementary realContext)
  | .ordered formula => PM.OrderedFormula.eraseElementary? formula

def injectOrderedElementary (formula : PM.Elementary realContext) :
    Envelope (ObjectSort := ObjectSort) (.ordered realContext 0) :=
  injectOrdered (ObjectSort := ObjectSort) (PM.OrderedFormula.embedElementary formula)

@[simp] theorem retract_injectOrderedElementary (formula : PM.Elementary realContext) :
    retractOrderedElementary? (injectOrderedElementary (ObjectSort := ObjectSort) formula) = some formula := rfl

def injectDescription (formula : Formula signature realContext apparentContext order) :
    Envelope (.description signature realContext apparentContext order) :=
  .description formula

def retractDescription :
    Envelope (ObjectSort := ObjectSort) (.description signature realContext apparentContext order) →
      Formula signature realContext apparentContext order
  | .description formula => formula

@[simp] theorem retract_injectDescription
    (formula : Formula signature realContext apparentContext order) :
    retractDescription (injectDescription formula) = formula := rfl

theorem injectDescription_injective {signature : Signature ObjectSort}
    {realContext apparentContext : List ObjectSort} {order : Nat} :
    Function.Injective
      (injectDescription (signature := signature) (realContext := realContext)
        (apparentContext := apparentContext) (order := order)) := by
  intro left right equality
  cases equality
  rfl

/-! ## Capture-safe operation available on the description family -/

/-- The envelope exposes the already canonical, capture-safe description
substitution without changing its indices or defining a new substitution
algorithm. -/
def substituteDescriptionEnvelope
    (substitution : Substitution signature realContext source target) :
    Envelope (.description signature realContext source order) →
      Envelope (.description signature realContext target order)
  | .description formula => .description (formula.substitute substitution)

@[simp] theorem injectDescription_substitute
    (substitution : Substitution signature realContext source target)
    (formula : Formula signature realContext source order) :
    injectDescription (formula.substitute substitution) =
      substituteDescriptionEnvelope substitution (injectDescription formula) := rfl

/-- Weakening is the canonical lifted substitution.  The equation documents
that the envelope does not alter de Bruijn shifting. -/
def weakenDescriptionEnvelope :
    Envelope (.description signature realContext apparentContext order) →
      Envelope (.description signature realContext (fresh :: apparentContext) order)
  | .description formula => .description formula.weaken

@[simp] theorem injectDescription_weaken
    {fresh : ObjectSort}
    (formula : Formula signature realContext apparentContext order) :
    injectDescription (formula.weaken (fresh := fresh)) =
      weakenDescriptionEnvelope (fresh := fresh) (injectDescription formula) := rfl

/-!
There is intentionally no rename/substitute operation for `Elementary` or
`OrderedFormula` here: their current canonical APIs do not expose a compatible
operation with the required common indices.  Adding one in this module would
be a new architecture, not a structural envelope.
-/

end PM.Experimental.UnifiedSyntaxEnvelope
