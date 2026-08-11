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

-- PM-CONTEXT-ITEM PM1:✱2·02 PM.FirstEdition.Volume1.Star2.star_2_02
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_02 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ⊃ₚ q)) :=
  PM.Derivation.star_1_3 (∼ₚ p) q

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·03 PM.FirstEdition.Volume1.Star2.star_2_03
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_03 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ ∼ₚ p)) :=
  PM.Derivation.star_1_4 (∼ₚ p) (∼ₚ q)

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·04 PM.FirstEdition.Volume1.Star2.star_2_04
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_04 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_5 (∼ₚ p) (∼ₚ q) r

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·05 PM.FirstEdition.Volume1.Star2.star_2_05
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_05 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_6 (∼ₚ p) q r

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·06 PM.FirstEdition.Volume1.Star2.star_2_06
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_06 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.detach (star_2_05 p q r)
    (star_2_04 (q ⊃ₚ r) (p ⊃ₚ q) (p ⊃ₚ r))

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

-- PM-CONTEXT-ITEM PM1:✱2·12 PM.FirstEdition.Volume1.Star2.star_2_12
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_12 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ ∼ₚ (∼ₚ p)) := by
  exact star_2_11 (∼ₚ p)

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·13 PM.FirstEdition.Volume1.Star2.star_2_13
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_13 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ (∼ₚ (∼ₚ p))) := by
  have hsum := PM.Derivation.star_1_6 p (∼ₚ p) (∼ₚ (∼ₚ (∼ₚ p)))
  have hstep := PM.Derivation.detach (star_2_12 (∼ₚ p)) hsum
  exact PM.Derivation.detach (star_2_11 p) hstep

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·14 PM.FirstEdition.Volume1.Star2.star_2_14
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_14 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (∼ₚ p) ⊃ₚ p) := by
  have hperm := PM.Derivation.star_1_4 p (∼ₚ (∼ₚ (∼ₚ p)))
  exact PM.Derivation.detach (star_2_13 p) hperm

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·15 PM.FirstEdition.Volume1.Star2.star_2_15
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_15 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p)) := by
  have line1 := star_2_05 (∼ₚ p) q (∼ₚ (∼ₚ q))
  have line2 := star_2_12 q
  have line3 := PM.Derivation.detach line2 line1
  have line4 := star_2_03 (∼ₚ p) (∼ₚ q)
  have line5 := star_2_05 (∼ₚ q) (∼ₚ (∼ₚ p)) p
  have line6 := PM.Derivation.detach (star_2_14 p) line5
  have line7 := star_2_05 (∼ₚ p ⊃ₚ q) (∼ₚ p ⊃ₚ ∼ₚ (∼ₚ q))
    (∼ₚ q ⊃ₚ ∼ₚ (∼ₚ p))
  have line8 := PM.Derivation.detach line4 line7
  have line9 := PM.Derivation.detach line3 line8
  have line10 := star_2_05 (∼ₚ p ⊃ₚ q) (∼ₚ q ⊃ₚ ∼ₚ (∼ₚ p)) (∼ₚ q ⊃ₚ p)
  have line11 := PM.Derivation.detach line6 line10
  exact PM.Derivation.detach line9 line11

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·16 PM.FirstEdition.Volume1.Star2.star_2_16
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_16 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p)) := by
  have line1 := PM.Derivation.detach (star_2_12 q)
    (star_2_05 p q (∼ₚ (∼ₚ q)))
  have line2 := star_2_03 p (∼ₚ q)
  have syll := PM.Derivation.detach line1
    (star_2_06 (p ⊃ₚ q) (p ⊃ₚ ∼ₚ (∼ₚ q)) (∼ₚ q ⊃ₚ ∼ₚ p))
  exact PM.Derivation.detach line2 syll

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·17 PM.FirstEdition.Volume1.Star2.star_2_17
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_17 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q)) := by
  have line1 := star_2_03 (∼ₚ q) p
  have line2 := PM.Derivation.detach (star_2_14 q)
    (star_2_05 p (∼ₚ (∼ₚ q)) q)
  have syll := PM.Derivation.detach line1
    (star_2_06 (∼ₚ q ⊃ₚ ∼ₚ p) (p ⊃ₚ ∼ₚ (∼ₚ q)) (p ⊃ₚ q))
  exact PM.Derivation.detach line2 syll

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·3 PM.FirstEdition.Volume1.Star2.star_2_3
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_3 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (p ∨ₚ (r ∨ₚ q))) :=
  PM.Derivation.detach
    (PM.Derivation.star_1_4 q r)
    (PM.Derivation.star_1_6 p (q ∨ₚ r) (r ∨ₚ q))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·31 PM.FirstEdition.Volume1.Star2.star_2_31
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_31 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r)) :=
  PM.Derivation.detach
    (PM.Derivation.detach
      (star_2_3 p q r)
      (PM.Derivation.detach
        (PM.Derivation.star_1_5 p r q)
        (star_2_05 (p ∨ₚ (q ∨ₚ r)) (p ∨ₚ (r ∨ₚ q)) (r ∨ₚ (p ∨ₚ q)))))
    (PM.Derivation.detach
      (PM.Derivation.star_1_4 r (p ∨ₚ q))
      (star_2_05 (p ∨ₚ (q ∨ₚ r)) (r ∨ₚ (p ∨ₚ q)) ((p ∨ₚ q) ∨ₚ r)))

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

-- PM-CONTEXT-ITEM PM1:✱2·38 PM.FirstEdition.Volume1.Star2.star_2_38
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_38 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) := by
  have permIn : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) := PM.Derivation.star_1_4 q p
  have permOut : ⊢ₚ ((p ∨ₚ r) ⊃ₚ (r ∨ₚ p)) := PM.Derivation.star_1_4 p r
  have line1 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach permIn (star_2_06 (q ∨ₚ p) (p ∨ₚ q) (p ∨ₚ r))
  have line2 : ⊢ₚ (((q ∨ₚ p) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) :=
    PM.Derivation.detach permOut (star_2_05 (q ∨ₚ p) (p ∨ₚ r) (r ∨ₚ p))
  have line3 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) :=
    PM.Derivation.detach line2
      (PM.Derivation.detach line1
        (star_2_06 ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))))
  have sum : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) := PM.Derivation.star_1_6 p q r
  exact PM.Derivation.detach sum
    (PM.Derivation.detach line3
      (star_2_05 (q ⊃ₚ r) ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·53 PM.FirstEdition.Volume1.Star2.star_2_53
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_53 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ (∼ₚ p ⊃ₚ q)) := by
  have lift : ⊢ₚ ((p ⊃ₚ ∼ₚ (∼ₚ p)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (∼ₚ (∼ₚ p) ∨ₚ q))) :=
    star_2_38 q p (∼ₚ (∼ₚ p))
  exact PM.Derivation.detach (star_2_12 p) lift

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·6 PM.FirstEdition.Volume1.Star2.star_2_6
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_6 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)) := by
  have line1 : ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ ((∼ₚ p ∨ₚ q) ⊃ₚ (q ∨ₚ q))) :=
    star_2_38 q (∼ₚ p) q
  have line2 : ⊢ₚ (((∼ₚ p ∨ₚ q) ⊃ₚ (q ∨ₚ q)) ⊃ₚ ((∼ₚ p ∨ₚ q) ⊃ₚ q)) :=
    PM.Derivation.detach (PM.Derivation.star_1_2 q)
      (star_2_05 (∼ₚ p ∨ₚ q) (q ∨ₚ q) q)
  exact PM.Derivation.detach line2
    (PM.Derivation.detach line1
      (star_2_06 (∼ₚ p ⊃ₚ q) ((∼ₚ p ∨ₚ q) ⊃ₚ (q ∨ₚ q)) ((∼ₚ p ∨ₚ q) ⊃ₚ q)))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·62 PM.FirstEdition.Volume1.Star2.star_2_62
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_62 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)) := by
  exact PM.Derivation.detach (star_2_6 p q)
    (PM.Derivation.detach (star_2_53 p q)
      (star_2_06 (p ∨ₚ q) (∼ₚ p ⊃ₚ q) ((p ⊃ₚ q) ⊃ₚ q)))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·621 PM.FirstEdition.Volume1.Star2.star_2_621
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_621 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∨ₚ q) ⊃ₚ q)) := by
  exact PM.Derivation.detach (star_2_62 p q)
    (star_2_04 (p ∨ₚ q) (p ⊃ₚ q) q)

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·73 PM.FirstEdition.Volume1.Star2.star_2_73
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_73 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r))) := by
  have first : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∨ₚ q) ⊃ₚ q)) := star_2_621 p q
  have second : ⊢ₚ (((p ∨ₚ q) ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r))) :=
    star_2_38 r (p ∨ₚ q) q
  have syll :
      ⊢ₚ ((((p ∨ₚ q) ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r))) ⊃ₚ
          (((p ⊃ₚ q) ⊃ₚ ((p ∨ₚ q) ⊃ₚ q)) ⊃ₚ
            ((p ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r))))) :=
    PM.Derivation.star_1_6 (∼ₚ (p ⊃ₚ q)) ((p ∨ₚ q) ⊃ₚ q)
      (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r))
  exact PM.Derivation.detach first (PM.Derivation.detach second syll)

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·74 PM.FirstEdition.Volume1.Star2.star_2_74
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_74 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))) := by
  have perm : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) := PM.Derivation.star_1_4 p q
  have sum : ⊢ₚ ((r ∨ₚ (p ∨ₚ q)) ⊃ₚ (r ∨ₚ (q ∨ₚ p))) :=
    PM.Derivation.detach perm (PM.Derivation.star_1_6 r (p ∨ₚ q) (q ∨ₚ p))
  have rotateIn : ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (r ∨ₚ (p ∨ₚ q))) :=
    PM.Derivation.star_1_4 (p ∨ₚ q) r
  have rotateOut : ⊢ₚ ((r ∨ₚ (q ∨ₚ p)) ⊃ₚ ((q ∨ₚ p) ∨ₚ r)) :=
    PM.Derivation.star_1_4 r (q ∨ₚ p)
  have half : ⊢ₚ ((r ∨ₚ (p ∨ₚ q)) ⊃ₚ ((q ∨ₚ p) ∨ₚ r)) :=
    PM.Derivation.detach sum
      (PM.Derivation.detach rotateOut
        (star_2_05 (r ∨ₚ (p ∨ₚ q)) (r ∨ₚ (q ∨ₚ p)) ((q ∨ₚ p) ∨ₚ r)))
  have swap : ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ ((q ∨ₚ p) ∨ₚ r)) :=
    PM.Derivation.detach rotateIn
      (PM.Derivation.detach half
        (star_2_05 ((p ∨ₚ q) ∨ₚ r) (r ∨ₚ (p ∨ₚ q)) ((q ∨ₚ p) ∨ₚ r)))
  have base : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (((q ∨ₚ p) ∨ₚ r) ⊃ₚ (p ∨ₚ r))) := star_2_73 q p r
  have inner :
      ⊢ₚ ((((q ∨ₚ p) ∨ₚ r) ⊃ₚ (p ∨ₚ r)) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach swap
      (star_2_06 ((p ∨ₚ q) ∨ₚ r) ((q ∨ₚ p) ∨ₚ r) (p ∨ₚ r))
  exact PM.Derivation.detach base
    (PM.Derivation.detach inner
      (star_2_05 (q ⊃ₚ p) (((q ∨ₚ p) ∨ₚ r) ⊃ₚ (p ∨ₚ r))
        (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·75 PM.FirstEdition.Volume1.Star2.star_2_75
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_75 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ (p ∨ₚ r))) := by
  have perm : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) := PM.Derivation.star_1_4 p q
  have fromDisj : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (∼ₚ q ⊃ₚ p)) := star_2_53 q p
  have hyp : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p)) :=
    PM.Derivation.detach perm
      (PM.Derivation.detach fromDisj
        (PM.Derivation.star_1_6 (∼ₚ (p ∨ₚ q)) (q ∨ₚ p) (∼ₚ q ⊃ₚ p)))
  have shifted :
      ⊢ₚ ((∼ₚ q ⊃ₚ p) ⊃ₚ (((p ∨ₚ ∼ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))) :=
    star_2_74 p (∼ₚ q) r
  have curried :
      ⊢ₚ ((p ∨ₚ q) ⊃ₚ (((p ∨ₚ ∼ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach hyp
      (PM.Derivation.detach shifted
        (PM.Derivation.star_1_6 (∼ₚ (p ∨ₚ q)) (∼ₚ q ⊃ₚ p)
          (((p ∨ₚ ∼ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ r))))
  have commuted :
      ⊢ₚ (((p ∨ₚ ∼ₚ q) ∨ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach curried
      (PM.Derivation.star_1_5 (∼ₚ (p ∨ₚ q)) (∼ₚ ((p ∨ₚ ∼ₚ q) ∨ₚ r)) (p ∨ₚ r))
  have assoc : ⊢ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∨ₚ ∼ₚ q) ∨ₚ r)) :=
    star_2_31 p (∼ₚ q) r
  have joined :
      ⊢ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach assoc
      (PM.Derivation.detach commuted
        (PM.Derivation.star_1_6 (∼ₚ (p ∨ₚ (q ⊃ₚ r))) ((p ∨ₚ ∼ₚ q) ∨ₚ r)
          ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))))
  exact PM.Derivation.detach joined
    (PM.Derivation.star_1_5 (∼ₚ (p ∨ₚ (q ⊃ₚ r))) (∼ₚ (p ∨ₚ q)) (p ∨ₚ r))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·76 PM.FirstEdition.Volume1.Star2.star_2_76
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_76 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) := by
  exact PM.Derivation.detach (star_2_75 p q r)
    (star_2_04 (p ∨ₚ q) (p ∨ₚ (q ⊃ₚ r)) (p ∨ₚ r))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·8 PM.FirstEdition.Volume1.Star2.star_2_8
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_8 {Γ} (q r s : PM.Elementary Γ) :
    ⊢ₚ ((q ∨ₚ r) ⊃ₚ ((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s))) := by
  have perm : ⊢ₚ ((q ∨ₚ r) ⊃ₚ (r ∨ₚ q)) :=
    PM.Derivation.star_1_4 q r
  have permFlipped : ⊢ₚ ((r ∨ₚ q) ∨ₚ ∼ₚ (q ∨ₚ r)) :=
    PM.Derivation.detach perm
      (PM.Derivation.star_1_4 (∼ₚ (q ∨ₚ r)) (r ∨ₚ q))
  have fiftyThree : ⊢ₚ ((r ∨ₚ q) ⊃ₚ (∼ₚ r ⊃ₚ q)) := star_2_53 r q
  have sumFiftyThree :
      ⊢ₚ (((r ∨ₚ q) ∨ₚ ∼ₚ (q ∨ₚ r)) ⊃ₚ ((∼ₚ r ⊃ₚ q) ∨ₚ ∼ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach fiftyThree
      (star_2_38 (∼ₚ (q ∨ₚ r)) (r ∨ₚ q) (∼ₚ r ⊃ₚ q))
  have line1 : ⊢ₚ ((∼ₚ r ⊃ₚ q) ∨ₚ ∼ₚ (q ∨ₚ r)) :=
    PM.Derivation.detach permFlipped sumFiftyThree
  have line2 : ⊢ₚ ((∼ₚ r ⊃ₚ q) ⊃ₚ ((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s))) :=
    star_2_38 s (∼ₚ r) q
  have sumLine2 :
      ⊢ₚ (((∼ₚ r ⊃ₚ q) ∨ₚ ∼ₚ (q ∨ₚ r)) ⊃ₚ
        (((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s)) ∨ₚ ∼ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach line2
      (star_2_38 (∼ₚ (q ∨ₚ r)) (∼ₚ r ⊃ₚ q) ((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s)))
  have line3 : ⊢ₚ (((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s)) ∨ₚ ∼ₚ (q ∨ₚ r)) :=
    PM.Derivation.detach line1 sumLine2
  exact PM.Derivation.detach line3
    (PM.Derivation.star_1_4
      ((∼ₚ r ∨ₚ s) ⊃ₚ (q ∨ₚ s)) (∼ₚ (q ∨ₚ r)))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·81 PM.FirstEdition.Volume1.Star2.star_2_81
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_81 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ (r ⊃ₚ s)) ⊃ₚ
      ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ r) ⊃ₚ (p ∨ₚ s)))) := by
  have line1 :
      ⊢ₚ ((q ⊃ₚ (r ⊃ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ (r ⊃ₚ s)))) :=
    PM.Derivation.star_1_6 p q (r ⊃ₚ s)
  have line2 :
      ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ (r ⊃ₚ s))) ⊃ₚ
        ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ r) ⊃ₚ (p ∨ₚ s)))) :=
    PM.Derivation.detach (star_2_76 p r s)
      (star_2_05 (p ∨ₚ q) (p ∨ₚ (r ⊃ₚ s)) ((p ∨ₚ r) ⊃ₚ (p ∨ₚ s)))
  exact PM.Derivation.detach line2
    (PM.Derivation.detach line1
      (star_2_06 (q ⊃ₚ (r ⊃ₚ s)) ((p ∨ₚ q) ⊃ₚ (p ∨ₚ (r ⊃ₚ s)))
        ((p ∨ₚ q) ⊃ₚ ((p ∨ₚ r) ⊃ₚ (p ∨ₚ s)))))

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·82 PM.FirstEdition.Volume1.Star2.star_2_82
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_82 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (((p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ ((p ∨ₚ q) ∨ₚ s))) := by
  have compose : ∀ A B C : Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C h₁ h₂
    exact PM.Derivation.detach h₁
      (PM.Derivation.detach h₂ (star_2_05 A B C))
  have printed :
      ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ
        ((p ∨ₚ (∼ₚ r ∨ₚ s)) ⊃ₚ (p ∨ₚ (q ∨ₚ s)))) :=
    PM.Derivation.detach (star_2_8 q r s)
      (star_2_81 p (q ∨ₚ r) (∼ₚ r ∨ₚ s) (q ∨ₚ s))
  have antecedent : ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))) :=
    star_2_32 p q r
  have innerAntecedent :
      ⊢ₚ (((p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ (p ∨ₚ (∼ₚ r ∨ₚ s))) :=
    star_2_32 p (∼ₚ r) s
  have conclusion : ⊢ₚ ((p ∨ₚ (q ∨ₚ s)) ⊃ₚ ((p ∨ₚ q) ∨ₚ s)) :=
    star_2_31 p q s
  have inner :
      ⊢ₚ (((p ∨ₚ (∼ₚ r ∨ₚ s)) ⊃ₚ (p ∨ₚ (q ∨ₚ s))) ⊃ₚ
        (((p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ ((p ∨ₚ q) ∨ₚ s))) :=
    compose _ _ _
      (PM.Derivation.detach innerAntecedent
        (star_2_06 ((p ∨ₚ ∼ₚ r) ∨ₚ s) (p ∨ₚ (∼ₚ r ∨ₚ s)) (p ∨ₚ (q ∨ₚ s))))
      (PM.Derivation.detach conclusion
        (star_2_05 ((p ∨ₚ ∼ₚ r) ∨ₚ s) (p ∨ₚ (q ∨ₚ s)) ((p ∨ₚ q) ∨ₚ s)))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱2·83 PM.FirstEdition.Volume1.Star2.star_2_83
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_83 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ
      ((p ⊃ₚ (r ⊃ₚ s)) ⊃ₚ (p ⊃ₚ (q ⊃ₚ s)))) := by
  have compose : ∀ A B C : Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C h₁ h₂
    exact PM.Derivation.detach h₁
      (PM.Derivation.detach h₂ (star_2_05 A B C))
  have printed :
      ⊢ₚ (((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ r) ⊃ₚ
        (((∼ₚ p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ ((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ s))) :=
    star_2_82 (∼ₚ p) (∼ₚ q) r s
  have antecedent :
      ⊢ₚ ((∼ₚ p ∨ₚ (∼ₚ q ∨ₚ r)) ⊃ₚ ((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ r)) :=
    star_2_31 (∼ₚ p) (∼ₚ q) r
  have innerAntecedent :
      ⊢ₚ ((∼ₚ p ∨ₚ (∼ₚ r ∨ₚ s)) ⊃ₚ ((∼ₚ p ∨ₚ ∼ₚ r) ∨ₚ s)) :=
    star_2_31 (∼ₚ p) (∼ₚ r) s
  have conclusion :
      ⊢ₚ (((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ s) ⊃ₚ (∼ₚ p ∨ₚ (∼ₚ q ∨ₚ s))) :=
    star_2_32 (∼ₚ p) (∼ₚ q) s
  have inner :
      ⊢ₚ ((((∼ₚ p ∨ₚ ∼ₚ r) ∨ₚ s) ⊃ₚ ((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ s)) ⊃ₚ
        ((∼ₚ p ∨ₚ (∼ₚ r ∨ₚ s)) ⊃ₚ (∼ₚ p ∨ₚ (∼ₚ q ∨ₚ s)))) :=
    compose _ _ _
      (PM.Derivation.detach innerAntecedent
        (star_2_06 (∼ₚ p ∨ₚ (∼ₚ r ∨ₚ s)) ((∼ₚ p ∨ₚ ∼ₚ r) ∨ₚ s)
          ((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ s)))
      (PM.Derivation.detach conclusion
        (star_2_05 (∼ₚ p ∨ₚ (∼ₚ r ∨ₚ s)) ((∼ₚ p ∨ₚ ∼ₚ q) ∨ₚ s)
          (∼ₚ p ∨ₚ (∼ₚ q ∨ₚ s))))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-ITEM PM1:✱3·01 PM.Elementary.conj
namespace PM.Elementary

def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

infixl:56 " ∧ₚ " => conj

end PM.Elementary

-- PM-CONTEXT-ITEM PM1:✱3·03 PM.FirstEdition.Volume1.Star3.star_3_03
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_03 {Γ : PM.RealContext} (hasRealVariable : Γ ≠ [])
    {φ ψ : PM.Elementary Γ}
    (hφ : PM.FormedDerivation φ) (hψ : PM.FormedDerivation ψ) :
    PM.FormedDerivation (PM.Elementary.conj φ ψ) := by
  refine ⟨?_, ?_⟩
  · exact PM.Formation.star_1_7
      (PM.Formation.star_1_72 hasRealVariable
        (PM.Formation.star_1_7 hφ.formation)
        (PM.Formation.star_1_7 hψ.formation))
  · have h1 : ⊢ₚ ((∼ₚ φ ∨ₚ ∼ₚ ψ) ∨ₚ ∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)) :=
      PM.FirstEdition.Volume1.Star2.star_2_11 (∼ₚ φ ∨ₚ ∼ₚ ψ)
    have h2 : ⊢ₚ (φ ⊃ₚ (ψ ⊃ₚ PM.Elementary.conj φ ψ)) :=
      PM.Derivation.star_1_11 hasRealVariable h1
        (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ φ) (∼ₚ ψ)
          (∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)))
    exact PM.Derivation.star_1_11 hasRealVariable hψ.derivation
      (PM.Derivation.star_1_11 hasRealVariable hφ.derivation h2)

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·1 PM.FirstEdition.Volume1.Star3.star_3_1
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := by
  simpa only [PM.Elementary.conj] using
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·11 PM.FirstEdition.Volume1.Star3.star_3_11
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ (p ∧ₚ q)) := by
  simpa only [PM.Elementary.conj] using
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·12 PM.FirstEdition.Volume1.Star3.star_3_12
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q)) :=
  PM.FirstEdition.Volume1.Star2.star_2_11 ((∼ₚ p) ∨ₚ (∼ₚ q))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·13 PM.FirstEdition.Volume1.Star3.star_3_13
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_13 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) :=
  PM.Derivation.detach (star_3_11 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_15 ((∼ₚ p) ∨ₚ (∼ₚ q)) (p ∧ₚ q))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·14 PM.FirstEdition.Volume1.Star3.star_3_14
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_14 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (p ∧ₚ q))) := by
  have hImp : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := star_3_1 p q
  have hTransp :
      ⊢ₚ ((∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) ⊃ₚ (∼ₚ (p ∧ₚ q))) :=
    PM.Derivation.detach hImp
      (PM.FirstEdition.Volume1.Star2.star_2_16 (p ∧ₚ q)
        (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))
  have hDN : ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))) :=
    PM.FirstEdition.Volume1.Star2.star_2_12 ((∼ₚ p) ∨ₚ (∼ₚ q))
  exact PM.Derivation.detach hTransp
    (PM.Derivation.detach hDN
      (PM.FirstEdition.Volume1.Star2.star_2_06 ((∼ₚ p) ∨ₚ (∼ₚ q))
        (∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) (∼ₚ (p ∧ₚ q))))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·2 PM.FirstEdition.Volume1.Star3.star_3_2
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_2 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ q))) :=
  PM.Derivation.detach (star_3_12 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ p) (∼ₚ q) (p ∧ₚ q))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·22 PM.FirstEdition.Volume1.Star3.star_3_22
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_22 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ p)) :=
  PM.Derivation.detach
    (PM.Derivation.detach (star_3_14 p q)
      (PM.Derivation.detach
        (PM.Derivation.detach
          (PM.Derivation.star_1_4 (∼ₚ q) (∼ₚ p))
          (PM.Derivation.detach (star_3_13 q p)
            (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
              ((∼ₚ q) ∨ₚ (∼ₚ p)) ((∼ₚ p) ∨ₚ (∼ₚ q)))))
        (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
          ((∼ₚ p) ∨ₚ (∼ₚ q)) (∼ₚ (p ∧ₚ q)))))
    (PM.FirstEdition.Volume1.Star2.star_2_17 (p ∧ₚ q) (q ∧ₚ p))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·26 PM.FirstEdition.Volume1.Star3.star_3_26
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_26 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ p) :=
  PM.Derivation.detach
    (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star2.star_2_02 q p)
      (PM.FirstEdition.Volume1.Star2.star_2_31 (∼ₚ p) (∼ₚ q) p))
    (PM.FirstEdition.Volume1.Star2.star_2_53 ((∼ₚ p) ∨ₚ (∼ₚ q)) p)

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·27 PM.FirstEdition.Volume1.Star3.star_3_27
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_27 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ q) :=
  PM.Derivation.detach (star_3_22 p q)
    (PM.Derivation.detach (star_3_26 q p)
      (PM.Derivation.star_1_6 (∼ₚ (p ∧ₚ q)) (q ∧ₚ p) q))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·31 PM.FirstEdition.Volume1.Star3.star_3_31
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_31 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) :=
  PM.Derivation.detach
    (PM.FirstEdition.Volume1.Star2.star_2_31 (∼ₚ p) (∼ₚ q) r)
    (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star2.star_2_53 ((∼ₚ p) ∨ₚ (∼ₚ q)) r)
      (PM.Derivation.star_1_6 (∼ₚ (p ⊃ₚ (q ⊃ₚ r)))
        (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ r) ((p ∧ₚ q) ⊃ₚ r)))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·33 PM.FirstEdition.Volume1.Star3.star_3_33
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_33 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r)) := by
  have minor : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
    PM.FirstEdition.Volume1.Star2.star_2_06 p q r
  have major :
      ⊢ₚ (((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) ⊃ₚ
            (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r))) :=
    star_3_31 (p ⊃ₚ q) (q ⊃ₚ r) (p ⊃ₚ r)
  match Γ, p, q, r, minor, major with
  | [], _, _, _, minor, major => exact PM.Derivation.star_1_1 minor major
  | (τ :: Δ), _, _, _, minor, major =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) minor major

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·34 PM.FirstEdition.Volume1.Star3.star_3_34
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_34 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r)) := by
  have minor : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
    PM.FirstEdition.Volume1.Star2.star_2_05 p q r
  have major :
      ⊢ₚ (((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) ⊃ₚ
            (((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r))) :=
    star_3_31 (q ⊃ₚ r) (p ⊃ₚ q) (p ⊃ₚ r)
  match Γ, p, q, r, minor, major with
  | [], _, _, _, minor, major => exact PM.Derivation.star_1_1 minor major
  | (τ :: Δ), _, _, _, minor, major =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) minor major

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·37 PM.FirstEdition.Volume1.Star3.star_3_37
namespace PM.FirstEdition.Volume1.Star3

opaque star_3_37 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ⊃ₚ ((p ∧ₚ (∼ₚ r)) ⊃ₚ (∼ₚ q)))


end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·45 PM.FirstEdition.Volume1.Star3.star_3_45
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_45 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∧ₚ r) ⊃ₚ (q ∧ₚ r))) := by
  have printedSyll : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r)))) :=
    PM.Derivation.detach (star_3_33 p q (∼ₚ r))
      (star_3_3 (p ⊃ₚ q) (q ⊃ₚ (∼ₚ r)) (p ⊃ₚ (∼ₚ r)))
  have transp : ⊢ₚ (((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ
        ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r))))) :=
    PM.FirstEdition.Volume1.Star2.star_2_16 (q ⊃ₚ (∼ₚ r)) (p ⊃ₚ (∼ₚ r))
  exact PM.Derivation.detach transp (PM.Derivation.detach printedSyll
    (PM.Derivation.detach
      (star_3_33 (p ⊃ₚ q) ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r)))
        ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r)))))
      (star_3_3 ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))))
        (((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r)))))
        ((p ⊃ₚ q) ⊃ₚ ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r))))))))

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱3·47 PM.FirstEdition.Volume1.Star3.star_3_47
namespace PM.FirstEdition.Volume1.Star3

theorem star_3_47 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s))) := by
  have syllOf :
      (∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B))) →
      ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro adjoin A B C h₁ h₂
    have k₁ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (A ⊃ₚ B)) := star_3_26 (A ⊃ₚ B) (B ⊃ₚ C)
    have k₂ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (B ⊃ₚ C)) := star_3_27 (A ⊃ₚ B) (B ⊃ₚ C)
    have k₃ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (A ⊃ₚ C)) :=
      PM.Derivation.detach k₂ (PM.Derivation.detach k₁
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C)) A B C))
    exact PM.Derivation.detach (adjoin _ _ h₁ h₂) k₃
  have printed :
      (∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B))) →
      (∀ W M : PM.Elementary Γ, (⊢ₚ M) → (⊢ₚ (W ⊃ₚ M))) →
      ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s))) := by
    intro adjoin carry
    have syll := syllOf adjoin
    have first : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (p ⊃ₚ r)) := star_3_26 (p ⊃ₚ r) (q ⊃ₚ s)
    have fact₁ : ⊢ₚ ((p ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ q))) := star_3_45 p r q
    have firstFact : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ q))) :=
      syll _ _ _ first fact₁
    have perm₁ : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((r ∧ₚ q) ⊃ₚ (q ∧ₚ r))) :=
      carry _ _ (star_3_22 r q)
    have line1 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r))) :=
      PM.Derivation.detach perm₁ (PM.Derivation.detach firstFact
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (p ∧ₚ q) (r ∧ₚ q) (q ∧ₚ r)))
    have second : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (q ⊃ₚ s)) := star_3_27 (p ⊃ₚ r) (q ⊃ₚ s)
    have fact₂ : ⊢ₚ ((q ⊃ₚ s) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (s ∧ₚ r))) := star_3_45 q s r
    have secondFact : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (s ∧ₚ r))) :=
      syll _ _ _ second fact₂
    have perm₂ : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((s ∧ₚ r) ⊃ₚ (r ∧ₚ s))) :=
      carry _ _ (star_3_22 s r)
    have line2 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))) :=
      PM.Derivation.detach perm₂ (PM.Derivation.detach secondFact
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (q ∧ₚ r) (s ∧ₚ r) (r ∧ₚ s)))
    have joined := adjoin _ _ line1 line2
    have readBack₁ := PM.Derivation.detach joined
      (star_3_26 (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r)))
        (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))))
    have readBack₂ := PM.Derivation.detach joined
      (star_3_27 (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r)))
        (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))))
    exact PM.Derivation.detach readBack₂ (PM.Derivation.detach readBack₁
      (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (p ∧ₚ q) (q ∧ₚ r) (r ∧ₚ s)))
  cases Γ with
  | nil =>
      have adjoin : ∀ A B : PM.Elementary [], (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) :=
        fun A B hA hB => PM.Derivation.detach hB (PM.Derivation.detach hA (star_3_2 A B))
      exact printed adjoin fun W M hM => syllOf adjoin _ _ _
        (PM.Derivation.detach hM (star_3_2 M W)) (star_3_26 M W)
  | cons τ Δ =>
      have adjoin : ∀ A B : PM.Elementary (τ :: Δ), (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) :=
        fun A B hA hB => (star_3_03 (List.cons_ne_nil τ Δ)
          ⟨PM.Formation.ofElementary A, hA⟩ ⟨PM.Formation.ofElementary B, hB⟩).derivation
      exact printed adjoin fun W M hM => syllOf adjoin _ _ _
        (PM.Derivation.detach hM (star_3_2 M W)) (star_3_26 M W)

end PM.FirstEdition.Volume1.Star3

-- PM-CONTEXT-ITEM PM1:✱4·01 PM.Elementary.equiv
namespace PM.Elementary

opaque equiv (p q : PM.Elementary Γ) : PM.Elementary Γ


end PM.Elementary

-- PM-CONTEXT-ITEM PM1:✱4·11 PM.FirstEdition.Volume1.Star4.star_4_11
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ≡ₚ (∼ₚ p ≡ₚ ∼ₚ q))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-ITEM PM1:✱4·12 PM.FirstEdition.Volume1.Star4.star_4_12
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ (∼ₚ q)) ≡ₚ (q ≡ₚ (∼ₚ p)))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-ITEM PM1:✱4·13 PM.FirstEdition.Volume1.Star4.star_4_13
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_13 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (p ≡ₚ (∼ₚ (∼ₚ p)))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-ITEM PM1:✱4·14 PM.FirstEdition.Volume1.Star4.star_4_14
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_14 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ≡ₚ ((p ∧ₚ ∼ₚ r) ⊃ₚ ∼ₚ q))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-ITEM PM1:✱4·15 PM.FirstEdition.Volume1.Star4.star_4_15
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_15 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ ∼ₚ r) ≡ₚ ((q ∧ₚ r) ⊃ₚ ∼ₚ p))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-ITEM PM1:✱4·22 PM.FirstEdition.Volume1.Star4.star_4_22
namespace PM.FirstEdition.Volume1.Star4

opaque star_4_22 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (PM.Elementary.equivChain p q r ⊃ₚ (p ≡ₚ r))


end PM.FirstEdition.Volume1.Star4

-- PM-CONTEXT-INTERFACE-SYNTAX PM1:✱4·01
infix:53 " ≡ₚ " => PM.Elementary.equiv
