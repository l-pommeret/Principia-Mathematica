import Principia.Architecture.CanonicalOrderedAdapters

/-!
# PM I, ✱11·32–341

Exact two-apparent-variable targets of the four quantified transport
propositions on p. 162.  No derivation is claimed until the corresponding
one-variable theorem can be iterated by the PM judgement itself.

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

/-!
The four targets above are intentionally not packaged in structures.  The
unary ✱10 contracts do not currently export a relation-of-derivation
constructor that iterates them beneath a second apparent binder.  Merely
storing a polymorphic provider for a unary theorem next to `target = target`
does not derive any of these four displayed assertions.
-/

end PM.Architecture.Star11Q280Kernel
