import Principia.Architecture.FirstOrderPrerequisites
import Principia.Syntax.CanonicalOrderedFormula

namespace PM.Architecture.CanonicalOrderedAdapters

open PM.CanonicalOrderedFormula

def boundIndex : BoundVar Δ .elementaryProposition → Nat
  | .zero => 0
  | .succ v => boundIndex v + 1

def ofApparent : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v)
  | .neg p => .neg (ofApparent p)
  | .disj p q => .disj (ofApparent p) (ofApparent q)

def ofFirstOrder : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparent body)
  | .sometimes body => .quantified .sometimes (ofApparent body)

def ofFirstOrderMatrix : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => smartNeg (ofFirstOrderMatrix p)
  | .disj p q => smartDisj (ofFirstOrderMatrix p) (ofFirstOrderMatrix q)

def ofSecondOrder : SecondOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrder body)
  | .sometimes body => .quantified .sometimes (ofFirstOrder body)

def ofSecondMatrix : FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrderMatrix body)
  | .sometimes body => .quantified .sometimes (ofFirstOrderMatrix body)

def ofThirdOrder : FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrix body)
  | .sometimes body => .quantified .sometimes (ofSecondMatrix body)

@[simp] theorem ofApparent_neg (p : Apparent Γ Δ) :
    ofApparent (∼ₐ p) = .neg (ofApparent p) := rfl

end PM.Architecture.CanonicalOrderedAdapters
