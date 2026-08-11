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

prefix:max "∼ₚ" => neg

infixl:55 " ∨ₚ " => disj

def imp (p q : Elementary Γ) : Elementary Γ := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Elementary
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

def ofElementary : {Γ : RealContext} → (p : Elementary Γ) → Formation p
  | _, .constant name => .constant name
  | _, .var x => .realVar x
  | _, .neg p => .star_1_7 (ofElementary p)
  | [], .disj p q => .star_1_71 (ofElementary p) (ofElementary q)
  | (_ :: _), .disj p q =>
      .star_1_72 (List.cons_ne_nil _ _) (ofElementary p) (ofElementary q)

end Formation

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/Formed.lean
namespace PM

structure FormedDerivation {Γ : RealContext} (p : Elementary Γ) : Prop where
  formation : Formation p
  derivation : Derivation p

end PM

-- PM-CONTEXT-ITEM PM1:✱1·2 PM.FirstEdition.Volume1.Star1.star_1_2
namespace PM.FirstEdition.Volume1.Star1

theorem star_1_2 (p : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ p) ⊃ₚ p) :=
  PM.Derivation.star_1_2 p

end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·3 PM.FirstEdition.Volume1.Star1.star_1_3
namespace PM.FirstEdition.Volume1.Star1

theorem star_1_3 (p q : PM.Elementary Γ) : ⊢ₚ (q ⊃ₚ (p ∨ₚ q)) :=
  PM.Derivation.star_1_3 p q

end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·4 PM.FirstEdition.Volume1.Star1.star_1_4
namespace PM.FirstEdition.Volume1.Star1

theorem star_1_4 (p q : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) :=
  PM.Derivation.star_1_4 p q

end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·5 PM.FirstEdition.Volume1.Star1.star_1_5
namespace PM.FirstEdition.Volume1.Star1

theorem star_1_5 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_5 p q r

end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱1·6 PM.FirstEdition.Volume1.Star1.star_1_6
namespace PM.FirstEdition.Volume1.Star1

theorem star_1_6 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_6 p q r

end PM.FirstEdition.Volume1.Star1

-- PM-CONTEXT-ITEM PM1:✱2·05 PM.FirstEdition.Volume1.Star2.star_2_05
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_05 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_6 (∼ₚ p) q r

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·07 PM.FirstEdition.Volume1.Star2.star_2_07
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_07 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (p ∨ₚ p)) :=
  PM.Derivation.star_1_3 p p

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·08 PM.FirstEdition.Volume1.Star2.star_2_08
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_08 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ p) :=
  PM.Derivation.detach (star_2_07 p)
    (PM.Derivation.detach (PM.Derivation.star_1_2 p)
      (star_2_05 p (p ∨ₚ p) p))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·1 PM.FirstEdition.Volume1.Star2.star_2_1
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_1 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ p ∨ₚ p) :=
  star_2_08 p

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·11 PM.FirstEdition.Volume1.Star2.star_2_11
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_11 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ p) := by
  have hperm := PM.Derivation.star_1_4 (∼ₚ p) p
  exact PM.Derivation.detach (star_2_1 p) hperm

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·3 PM.FirstEdition.Volume1.Star2.star_2_3
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_3 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (p ∨ₚ (r ∨ₚ q))) :=
  PM.Derivation.detach
    (PM.Derivation.star_1_4 q r)
    (PM.Derivation.star_1_6 p (q ∨ₚ r) (r ∨ₚ q))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·32 PM.FirstEdition.Volume1.Star2.star_2_32
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_32 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))) :=
  PM.Derivation.detach
    (PM.Derivation.detach
      (PM.Derivation.star_1_4 (p ∨ₚ q) r)
      (PM.Derivation.detach
        (PM.Derivation.star_1_5 r p q)
        (star_2_05 ((p ∨ₚ q) ∨ₚ r) (r ∨ₚ (p ∨ₚ q)) (p ∨ₚ (r ∨ₚ q)))))
    (PM.Derivation.detach
      (star_2_3 p r q)
      (star_2_05 ((p ∨ₚ q) ∨ₚ r) (p ∨ₚ (r ∨ₚ q)) (p ∨ₚ (q ∨ₚ r))))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱3·01 PM.Elementary.conj
namespace PM.Elementary

def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

infixl:56 " ∧ₚ " => conj

end PM.Elementary
