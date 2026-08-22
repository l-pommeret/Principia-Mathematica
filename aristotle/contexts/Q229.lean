-- PM-CONTEXT-FOUNDATION Principia/Syntax/Formula.lean
namespace PM

inductive RealType where
  | elementaryProposition : RealType
  deriving DecidableEq, Repr

abbrev RealContext := List RealType

inductive RealVar : (Γ : RealContext) → RealType → Type where
  | zero : RealVar (τ :: Γ) τ
  | succ : RealVar Γ τ → RealVar (σ :: Γ) τ
  deriving DecidableEq, Repr

inductive Elementary : RealContext → Type where
  | constant : String → Elementary Γ
  | var : RealVar Γ .elementaryProposition → Elementary Γ
  | neg : Elementary Γ → Elementary Γ
  | disj : Elementary Γ → Elementary Γ → Elementary Γ
  deriving DecidableEq, Repr

namespace Elementary

abbrev SchemaAssignment (Γ Ξ : RealContext) :=
  RealVar Γ .elementaryProposition → Elementary Ξ

def schemaInstance (σ : SchemaAssignment Γ Ξ) : Elementary Γ → Elementary Ξ
  | .constant name => .constant name
  | .var v => σ v
  | .neg proposition => .neg (schemaInstance σ proposition)
  | .disj left right => .disj (schemaInstance σ left) (schemaInstance σ right)

prefix:max "∼ₚ" => neg

infixl:55 " ∨ₚ " => disj

def imp (p q : Elementary Γ) : Elementary Γ := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Elementary
end PM

-- PM-CONTEXT-FOUNDATION Principia/Syntax/Printed.lean
namespace PM

structure PrintedFormula where
  source : String
  deriving DecidableEq, Repr

def pmPrinted (source : String) : PrintedFormula := ⟨source⟩

structure ElementaryReading (Γ : RealContext) where
  printed : PrintedFormula
  parsed : Elementary Γ
  scopeReading : String
  deriving Repr

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/System.lean
namespace PM

inductive Derivation : {Γ : RealContext} → Elementary Γ → Prop where

  | star_1_1 {p q : Elementary []} :
      Derivation p → Derivation (p ⊃ₚ q) → Derivation q

  | star_1_11 {Γ : RealContext} {φ ψ : Elementary Γ}
      (hasRealVariable : Γ ≠ []) :
      Derivation φ → Derivation (φ ⊃ₚ ψ) → Derivation ψ

  | star_1_2 {Γ : RealContext} (p : Elementary Γ) :
      Derivation ((p ∨ₚ p) ⊃ₚ p)

  | star_1_3 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation (q ⊃ₚ (p ∨ₚ q))

  | star_1_4 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p))

  | star_1_5 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r)))

  | star_1_6 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)))

notation:45 "⊢ₚ " p => Derivation p

namespace Derivation

theorem instantiateSchema {Γ Ξ : PM.RealContext}
    (σ : PM.Elementary.SchemaAssignment Γ Ξ) {p : PM.Elementary Γ}
    (proof : PM.Derivation p) :
    PM.Derivation (PM.Elementary.schemaInstance σ p) := by
  induction proof with
  | star_1_1 hp hpq ihp ihpq =>
      cases Ξ with
      | nil => exact PM.Derivation.star_1_1 (ihp σ) (ihpq σ)
      | cons τ Δ =>
          exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) (ihp σ) (ihpq σ)
  | star_1_11 _ hp hpq ihp ihpq =>
      cases Ξ with
      | nil => exact PM.Derivation.star_1_1 (ihp σ) (ihpq σ)
      | cons τ Δ =>
          exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) (ihp σ) (ihpq σ)
  | star_1_2 p =>
      exact PM.Derivation.star_1_2 (Γ := Ξ) (PM.Elementary.schemaInstance σ p)
  | star_1_3 p q =>
      exact PM.Derivation.star_1_3 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
  | star_1_4 p q =>
      exact PM.Derivation.star_1_4 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
  | star_1_5 p q r =>
      exact PM.Derivation.star_1_5 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r)
  | star_1_6 p q r =>
      exact PM.Derivation.star_1_6 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r)

theorem detach {Γ : PM.RealContext} {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hφψ : PM.Derivation (φ ⊃ₚ ψ)) :
    PM.Derivation ψ := by
  match Γ, φ, ψ, hφ, hφψ with
  | [], φ, ψ, hφ, hφψ => exact PM.Derivation.star_1_1 hφ hφψ
  | (τ :: Δ), φ, ψ, hφ, hφψ =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hφ hφψ

end Derivation

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/Formation.lean
namespace PM

inductive Formation : {Γ : RealContext} → Elementary Γ → Prop where

  | constant (name : String) : Formation (.constant name)

  | realVar (x : RealVar Γ .elementaryProposition) : Formation (.var x)

  | star_1_7 (hp : Formation p) : Formation (Elementary.neg p)

  | star_1_71 (hp : Formation (Γ := []) p) (hq : Formation (Γ := []) q) :
      Formation (Elementary.disj p q)

  | star_1_72 (hasRealVariable : Γ ≠ [])
      (hφ : Formation (Γ := Γ) φ) (hψ : Formation (Γ := Γ) ψ) :
      Formation (Elementary.disj φ ψ)

namespace Formation

def star_1_7_reading (p : Elementary Γ) : ElementaryReading Γ where
  printed := pmPrinted "If p is an elementary proposition, ∼p is an elementary proposition. Pp."
  parsed := ∼ₚ p
  scopeReading := "Negation applies to the elementary proposition p; the rule licenses formation of ∼p."

def star_1_71_reading (p q : Elementary []) : ElementaryReading [] where
  printed := pmPrinted "If p and q are elementary propositions, p ∨ q is an elementary proposition. Pp."
  parsed := p ∨ₚ q
  scopeReading := "The rule forms the disjunction p ∨ q of two definite elementary propositions."

def star_1_72_reading (φ ψ : Elementary Γ) : ElementaryReading Γ where
  printed := pmPrinted "If φp and ψp are elementary propositional functions which take elementary propositions as arguments, φp ∨ ψp is an elementary propositional function. Pp."
  parsed := φ ∨ₚ ψ
  scopeReading := "The two functions share their elementary-proposition argument; disjunction combines their values."

def ofElementaryNil (p : Elementary []) : Formation p :=
  Elementary.rec
    (fun name => .constant name)
    (fun x => .realVar x)
    (fun _ hp => .star_1_7 hp)
    (fun _ _ hp hq => .star_1_71 hp hq)
    p

def ofElementaryCons (head : RealType) (tail : RealContext)
    (p : Elementary (head :: tail)) : Formation p :=
  Elementary.rec
    (fun name => .constant name)
    (fun x => .realVar x)
    (fun _ hp => .star_1_7 hp)
    (fun _ _ hp hq =>
      .star_1_72 (fun equality => nomatch equality) hp hq)
    p

def ofElementary : {Γ : RealContext} → (p : Elementary Γ) → Formation p
  | [], p => ofElementaryNil p
  | head :: tail, p => ofElementaryCons head tail p

macro_rules
  | `(term| match $x:term with
      | [], .disj p q => .star_1_71
      | (_ :: _), .disj p q =>
          .star_1_72 (List.cons_ne_nil _ _)) => `($x)

end Formation

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/Formed.lean
namespace PM

structure FormedDerivation {Γ : RealContext} (p : Elementary Γ) : Prop where
  formation : Formation p
  derivation : Derivation p

end PM

-- PM-CONTEXT-ELIMINABLE-DEFINITIONS ✱3·01-✱3·02
namespace PM.Elementary

def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

infixl:56 " ∧ₚ " => conj

def impChain (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  conj (p ⊃ₚ q) (q ⊃ₚ r)

end PM.Elementary

-- PM-CONTEXT-ITEM PM1:✱1·2 PM.FirstEdition.Volume1.Star1.star_1_2
namespace PM.FirstEdition.Volume1.Star1

axiom star_1_2 (p : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ p) ⊃ₚ p)


end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·3 PM.FirstEdition.Volume1.Star1.star_1_3
namespace PM.FirstEdition.Volume1.Star1

axiom star_1_3 (p q : PM.Elementary Γ) : ⊢ₚ (q ⊃ₚ (p ∨ₚ q))


end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·4 PM.FirstEdition.Volume1.Star1.star_1_4
namespace PM.FirstEdition.Volume1.Star1

axiom star_1_4 (p q : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p))


end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·5 PM.FirstEdition.Volume1.Star1.star_1_5
namespace PM.FirstEdition.Volume1.Star1

axiom star_1_5 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r)))


end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·6 PM.FirstEdition.Volume1.Star1.star_1_6
namespace PM.FirstEdition.Volume1.Star1

axiom star_1_6 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)))


end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱2·02 PM.FirstEdition.Volume1.Star2.star_2_02
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_02 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·03 PM.FirstEdition.Volume1.Star2.star_2_03
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_03 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ ∼ₚ p))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·04 PM.FirstEdition.Volume1.Star2.star_2_04
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_04 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·05 PM.FirstEdition.Volume1.Star2.star_2_05
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_05 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·06 PM.FirstEdition.Volume1.Star2.star_2_06
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_06 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·07 PM.FirstEdition.Volume1.Star2.star_2_07
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_07 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (p ∨ₚ p))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·08 PM.FirstEdition.Volume1.Star2.star_2_08
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_08 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ p)


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·1 PM.FirstEdition.Volume1.Star2.star_2_1
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_1 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ p ∨ₚ p)


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·11 PM.FirstEdition.Volume1.Star2.star_2_11
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_11 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ p)


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·12 PM.FirstEdition.Volume1.Star2.star_2_12
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_12 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ ∼ₚ (∼ₚ p))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·13 PM.FirstEdition.Volume1.Star2.star_2_13
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_13 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ (∼ₚ (∼ₚ p)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·14 PM.FirstEdition.Volume1.Star2.star_2_14
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_14 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (∼ₚ p) ⊃ₚ p)


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·15 PM.FirstEdition.Volume1.Star2.star_2_15
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_15 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·16 PM.FirstEdition.Volume1.Star2.star_2_16
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_16 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·17 PM.FirstEdition.Volume1.Star2.star_2_17
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_17 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·3 PM.FirstEdition.Volume1.Star2.star_2_3
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_3 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (p ∨ₚ (r ∨ₚ q)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·31 PM.FirstEdition.Volume1.Star2.star_2_31
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_31 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·32 PM.FirstEdition.Volume1.Star2.star_2_32
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_32 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·38 PM.FirstEdition.Volume1.Star2.star_2_38
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_38 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·4 PM.FirstEdition.Volume1.Star2.star_2_4
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_4 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (p ∨ₚ q)) ⊃ₚ (p ∨ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·42 PM.FirstEdition.Volume1.Star2.star_2_42
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_42 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ∨ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·43 PM.FirstEdition.Volume1.Star2.star_2_43
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_43 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·53 PM.FirstEdition.Volume1.Star2.star_2_53
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_53 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ (∼ₚ p ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·6 PM.FirstEdition.Volume1.Star2.star_2_6
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_6 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·62 PM.FirstEdition.Volume1.Star2.star_2_62
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_62 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·621 PM.FirstEdition.Volume1.Star2.star_2_621
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_621 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∨ₚ q) ⊃ₚ q))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·73 PM.FirstEdition.Volume1.Star2.star_2_73
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_73 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·74 PM.FirstEdition.Volume1.Star2.star_2_74
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_74 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·75 PM.FirstEdition.Volume1.Star2.star_2_75
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_75 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ (p ∨ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·76 PM.FirstEdition.Volume1.Star2.star_2_76
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_76 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·77 PM.FirstEdition.Volume1.Star2.star_2_77
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_77 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·8 PM.FirstEdition.Volume1.Star2.star_2_8
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_8 {Γ} (q r s : PM.Elementary Γ) :
    ⊢ₚ ((q ∨ₚ r) ⊃ₚ ((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·81 PM.FirstEdition.Volume1.Star2.star_2_81
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_81 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ (r ⊃ₚ s)) ⊃ₚ
      ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ r) ⊃ₚ (p ∨ₚ s))))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·82 PM.FirstEdition.Volume1.Star2.star_2_82
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_82 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (((p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ ((p ∨ₚ q) ∨ₚ s)))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·83 PM.FirstEdition.Volume1.Star2.star_2_83
namespace PM.FirstEdition.Volume1.Star2

axiom star_2_83 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ
      ((p ⊃ₚ (r ⊃ₚ s)) ⊃ₚ (p ⊃ₚ (q ⊃ₚ s))))


end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱3·1 PM.FirstEdition.Volume1.Star3.star_3_1
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·11 PM.FirstEdition.Volume1.Star3.star_3_11
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ (p ∧ₚ q))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·12 PM.FirstEdition.Volume1.Star3.star_3_12
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·13 PM.FirstEdition.Volume1.Star3.star_3_13
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_13 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·14 PM.FirstEdition.Volume1.Star3.star_3_14
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_14 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (p ∧ₚ q)))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·2 PM.FirstEdition.Volume1.Star3.star_3_2
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_2 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ q)))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·22 PM.FirstEdition.Volume1.Star3.star_3_22
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_22 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ p))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·26 PM.FirstEdition.Volume1.Star3.star_3_26
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_26 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ p)


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·27 PM.FirstEdition.Volume1.Star3.star_3_27
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_27 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ q)


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·31 PM.FirstEdition.Volume1.Star3.star_3_31
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_31 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·43 PM.FirstEdition.Volume1.Star3.star_3_43
namespace PM.FirstEdition.Volume1.Star3

axiom star_3_43 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ∧ₚ r)))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱4·01 PM.Elementary.equiv
namespace PM.Elementary

def equiv (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  (p ⊃ₚ q) ∧ₚ (q ⊃ₚ p)

infix:53 " ≡ₚ " => equiv

end PM.Elementary

-- PM-CONTEXT-ITEM PM1:✱4·02 PM.Elementary.equivChain
namespace PM.Elementary

def equivChain (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  (p ≡ₚ q) ∧ₚ (q ≡ₚ r)

end PM.Elementary
