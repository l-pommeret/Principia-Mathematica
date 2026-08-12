import Principia.Syntax.Apparent

namespace PM.CanonicalOrderedFormula

/-! Canonical, order-unbounded syntax for the binder-sensitive ✱9 reductions.
It is syntax only: it carries neither assertions nor inference rules. -/

inductive Quantifier where
  | always | sometimes
  deriving DecidableEq, Repr

inductive Raw : RealContext → Type where
  | elementary : Elementary Γ → Raw Γ
  | bound : Nat → Raw Γ
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

def openOuter : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary p => .elementary
      (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  | .bound 0 => .bound 0
  | .bound 1 => .elementary (.var .zero)
  | .bound (index + 2) => .bound (index + 1)
  | .quantified q body => .quantified q (openOuter body)
  | .neg p => .neg (openOuter p)
  | .disj p q => .disj (openOuter p) (openOuter q)

/-- Reify an elementary formula over a leading real variable as Raw syntax
under one additional outer binder. -/
def abstractElementary : Elementary (.elementaryProposition :: Γ) → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var .zero => .bound 1
  | .var (.succ v) => .elementary (.var v)
  | .neg p => .neg (abstractElementary p)
  | .disj p q => .disj (abstractElementary p) (abstractElementary q)

def shiftBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => if cutoff ≤ index then .bound (index + 1) else .bound index
  | .quantified q body => .quantified q (shiftBoundAt (cutoff + 1) body)
  | .neg p => .neg (shiftBoundAt cutoff p)
  | .disj p q => .disj (shiftBoundAt cutoff p) (shiftBoundAt cutoff q)

def weakenBound (p : Raw Γ) : Raw Γ := shiftBoundAt 0 p

/-- Capture-safe renaming of apparent binder indices.  Under a quantifier the
newly bound index remains zero and every older index is renamed through the
lifted map. -/
def renameBound (ρ : Nat → Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => .bound (ρ index)
  | .quantified q body =>
      .quantified q (renameBound (fun index =>
        match index with | 0 => 0 | n + 1 => ρ n + 1) body)
  | .neg p => .neg (renameBound ρ p)
  | .disj p q => .disj (renameBound ρ p) (renameBound ρ q)

def smartNeg : Raw Γ → Raw Γ
  | .quantified .always body => .quantified .sometimes (smartNeg body)
  | .quantified .sometimes body => .quantified .always (smartNeg body)
  | proposition => .neg proposition

def rawSize : Raw Γ → Nat
  | .elementary _ | .bound _ => 1
  | .quantified _ p | .neg p => rawSize p + 1
  | .disj p q => rawSize p + rawSize q + 1

def smartDisjAux : Nat → Raw Γ → Raw Γ → Raw Γ
  | 0, p, q => .disj p q
  | fuel + 1, .quantified .always p, .quantified .sometimes q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified .sometimes p, .quantified .always q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified q p, r =>
      .quantified q (smartDisjAux fuel p (weakenBound r))
  | fuel + 1, p, .quantified q r =>
      .quantified q (smartDisjAux fuel (weakenBound p) r)
  | _ + 1, p, q => .disj p q

def smartDisj (p q : Raw Γ) : Raw Γ :=
  smartDisjAux (rawSize p + rawSize q) p q

def smartImp (p q : Raw Γ) : Raw Γ := smartDisj (smartNeg p) q

@[simp] theorem shiftBoundAt_elementary (p : Elementary Γ) :
    shiftBoundAt cutoff (.elementary p) = .elementary p := rfl

@[simp] theorem smartNeg_always (p : Raw Γ) :
    smartNeg (.quantified .always p) = .quantified .sometimes (smartNeg p) := rfl

end PM.CanonicalOrderedFormula
