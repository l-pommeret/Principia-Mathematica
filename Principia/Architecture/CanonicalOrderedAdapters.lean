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

def ofThirdOrderFormula : FirstOrderMatrix.ThirdOrderFormula Γ Δ → Raw Γ
  | .quantified p => ofThirdOrder p
  | .neg p => .neg (ofThirdOrderFormula p)
  | .disj p q => .disj (ofThirdOrderFormula p) (ofThirdOrderFormula q)

def ofOrdered : OrderedFormula Γ order → Raw Γ
  | .elementary p => .elementary p
  | .firstOrder p => ofFirstOrder p
  | .firstOrderMatrix p => ofFirstOrderMatrix p
  | .secondOrder p => ofSecondOrder p
  | .secondOrderMatrix p => ofSecondMatrix p
  | .thirdOrderMatrix p => ofThirdOrder p
  | .thirdOrderFormula p => ofThirdOrderFormula p
  | .neg p => .neg (ofOrdered p)
  | .disj _ p q => .disj (ofOrdered p) (ofOrdered q)

/-- The four named matrix occurrences in the printed lines (3)–(7) of
✱9·21.  Their de Bruijn positions are obtained directly from the concrete
`star_9_21_line3_matrix` construction: `x = 1`, `y = 0`, and `z` remains a
real variable in the ambient context. -/
def star_9_21_phi_x_raw (φ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.succ .zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal φ))

def star_9_21_psi_x_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.succ .zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal ψ))

def star_9_21_phi_y_raw (φ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal φ))

def star_9_21_psi_z_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.ofElementary (Apparent.openHead ψ) :
    Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: .elementaryProposition :: []))

/-- Close the displayed leading real variable in a source-labelled Raw
matrix.  Repetition is explicit at each printed binder; no implicit context
coercion is involved. -/
def closeLeadingRaw (p : Raw (.elementaryProposition :: Γ)) : Raw Γ :=
  abstractOuter p

def star_9_21_phi_x_closed_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_phi_x_raw φ)

def star_9_21_psi_x_closed_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_psi_x_raw ψ)

def star_9_21_phi_y_closed_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_phi_y_raw φ)

def star_9_21_psi_z_closed_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_psi_z_raw ψ)

@[simp] theorem ofApparent_neg (p : Apparent Γ Δ) :
    ofApparent (∼ₐ p) = .neg (ofApparent p) := rfl

/-- Canonical embedding commutes with the capture-safe outer real abstraction
when an apparent binder is already open. -/
theorem ofApparent_abstractRealOuter
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    ofApparent (Apparent.abstractRealOuter p) =
      abstractOuter (ofApparent p) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ predecessor => rfl
  | neg proposition ih =>
      simp [ofApparent, Apparent.abstractRealOuter, abstractOuter,
        abstractOuterAt, ih]
  | disj left right ihLeft ihRight =>
      simp [ofApparent, Apparent.abstractRealOuter, abstractOuter,
        abstractOuterAt, ihLeft, ihRight]

theorem smartNeg_abstractOuter_ofApparent
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    smartNeg (abstractOuter (ofApparent p)) =
      abstractOuter (smartNeg (ofApparent p)) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable => cases boundVariable <;> rfl
  | neg proposition ih => simp [ofApparent, smartNeg, abstractOuter, abstractOuterAt]
  | disj left right ihLeft ihRight =>
      simp [ofApparent, smartNeg, abstractOuter, abstractOuterAt]

/-- Canonical Raw embedding of printed line (4) of ✱9·21.  The subsequent
definitions ✱9·06, ✱1·01 and ✱9·08 are represented by `smartNeg` and
`smartDisj`; this declaration itself makes no assertion or normalization
claim. -/
def star_9_21_line4_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofThirdOrder (FirstOrderMatrix.abstractThirdOuter
    (PM.Quantified.sometimes
      (PM.Architecture.FirstOrderPrerequisites.star_9_21_line3_matrix φ ψ)))

end PM.Architecture.CanonicalOrderedAdapters
