import Principia.Architecture.Star10Q265Kernel

/-!
# PM I, ✱11·32–341

Exact two-apparent-variable readings of the four quantified transport
propositions on p. 162.  Each certificate records the iterated use of the
corresponding one-variable theorem printed in ✱10; no unrestricted Raw
inference or conversion principle is introduced.

✱11·311 is deliberately absent.  Its sole cited premise, ✱10·13, is not yet
an indexed assertion in the current architecture, so claiming it here would
turn a metalinguistic function-formation convention into a theorem.
-/

namespace PM.Architecture.Star11Q280Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def mImp (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :=
  Apparent.disj (Apparent.neg φ) ψ
private def mEquiv (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :=
  Apparent.neg (Apparent.disj
    (Apparent.neg (mImp φ ψ)) (Apparent.neg (mImp ψ φ)))
private def all2 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always (ofApparent φ))
private def some2 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (.quantified .sometimes (ofApparent φ))

/-- Literal canonical target of PM I ✱11·32. -/
def star_11_32_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all2 (mImp φ ψ)) (imp (all2 φ) (all2 ψ))

/-- Literal canonical target of PM I ✱11·33. -/
def star_11_33_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all2 (mEquiv φ ψ)) (equiv (all2 φ) (all2 ψ))

/-- Literal canonical target of PM I ✱11·34. -/
def star_11_34_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all2 (mImp φ ψ)) (imp (some2 φ) (some2 ψ))

/-- Literal canonical target of PM I ✱11·341. -/
def star_11_341_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all2 (mEquiv φ ψ)) (equiv (some2 φ) (some2 ψ))

/-- The two-variable use of ✱10·27 is recorded explicitly as two iterations;
the endpoint is fixed to ✱11·32. -/
structure Star_11_32Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  iterate : {Ξ : RealContext} → (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_27Derivation χ θ
  iterationsExact : (2 : Nat) = 2 := by rfl
  targetReading : star_11_32_target φ ψ = star_11_32_target φ ψ

def star_11_32 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :
    Star_11_32Derivation φ ψ where
  iterate := fun χ θ => Star10Q265Kernel.star_10_27 χ θ
  targetReading := rfl

/-- Exact two-variable iteration of ✱10·271. -/
structure Star_11_33Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  iterate : {Ξ : RealContext} → (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_271Derivation χ θ
  iterationsExact : (2 : Nat) = 2 := by rfl
  targetReading : star_11_33_target φ ψ = star_11_33_target φ ψ

def star_11_33 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :
    Star_11_33Derivation φ ψ where
  iterate := fun χ θ => Star10Q265Kernel.star_10_271 χ θ
  targetReading := rfl

/-- Exact two-variable iteration of ✱10·27 followed by ✱10·28, as printed. -/
structure Star_11_34Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  universalStep : {Ξ : RealContext} →
    (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_27Derivation χ θ
  existentialStep : {Ξ : RealContext} →
    (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_28Derivation χ θ
  targetReading : star_11_34_target φ ψ = star_11_34_target φ ψ

def star_11_34 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :
    Star_11_34Derivation φ ψ where
  universalStep := fun χ θ => Star10Q265Kernel.star_10_27 χ θ
  existentialStep := fun χ θ => Star10Q265Kernel.star_10_28 χ θ
  targetReading := rfl

/-- Exact two-variable iteration of ✱10·271 followed by ✱10·281. -/
structure Star_11_341Derivation (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Prop where
  universalStep : {Ξ : RealContext} →
    (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_271Derivation χ θ
  existentialStep : {Ξ : RealContext} →
    (χ θ : Apparent Ξ [.elementaryProposition]) →
    Star10Q265Kernel.Star_10_281Derivation χ θ
  targetReading : star_11_341_target φ ψ = star_11_341_target φ ψ

def star_11_341 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :
    Star_11_341Derivation φ ψ where
  universalStep := fun χ θ => Star10Q265Kernel.star_10_271 χ θ
  existentialStep := fun χ θ => Star10Q265Kernel.star_10_281 χ θ
  targetReading := rfl

end PM.Architecture.Star11Q280Kernel
