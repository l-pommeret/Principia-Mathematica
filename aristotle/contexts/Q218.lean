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
  | star_1_2 p => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_2 (Γ := Ξ) (PM.Elementary.schemaInstance σ p))
  | star_1_3 p q => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_3 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q))
  | star_1_4 p q => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_4 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q))
  | star_1_5 p q r => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_5 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r))
  | star_1_6 p q r => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_6 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r))

theorem detach {Γ : PM.RealContext} {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hφψ : PM.Derivation (φ ⊃ₚ ψ)) :
    PM.Derivation ψ := by
  match Γ, φ, ψ, hφ, hφψ with
  | [], φ, ψ, hφ, hφψ => exact PM.Derivation.star_1_1 hφ hφψ
  | (τ :: Δ), φ, ψ, hφ, hφψ =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hφ hφψ

end Derivation

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
