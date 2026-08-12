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

/-- Depth-indexed embedding used when an apparent matrix is already beneath
canonical Raw binders. -/
def ofApparentAt (depth : Nat) : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v + depth)
  | .neg p => .neg (ofApparentAt depth p)
  | .disj p q => .disj (ofApparentAt depth p) (ofApparentAt depth q)

def ofFirstOrderAt (depth : Nat) : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparentAt (depth + 1) body)
  | .sometimes body => .quantified .sometimes (ofApparentAt (depth + 1) body)

def ofFirstOrder : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparent body)
  | .sometimes body => .quantified .sometimes (ofApparent body)

def ofFirstOrderMatrix : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => smartNeg (ofFirstOrderMatrix p)
  | .disj p q => smartDisj (ofFirstOrderMatrix p) (ofFirstOrderMatrix q)

/-- Scope-aware presentation kept distinct from the historical canonical
embedding while binder-sensitive ✱9 derivations are migrated. -/
def ofFirstOrderMatrixScoped : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => smartNeg (ofFirstOrderMatrixScoped p)
  | .disj p q =>
      smartDisjScoped (ofFirstOrderMatrixScoped p) (ofFirstOrderMatrixScoped q)

/-- Literal display embedding: unlike the normalizing embeddings, this keeps
matrix negation and disjunction as explicit Raw redex nodes. -/
def ofFirstOrderMatrixRedex : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => .neg (ofFirstOrderMatrixRedex p)
  | .disj p q =>
      .disj (ofFirstOrderMatrixRedex p) (ofFirstOrderMatrixRedex q)

structure ScopedFirstOrderMatrixReification
    (Δ : BoundContext) (raw : Raw Γ) where
  formula : FirstOrderMatrix Γ Δ
  roundTrip : ofFirstOrderMatrixScoped formula = raw

def reifyFirstOrderScoped (p : FirstOrder Γ Δ) :
    ScopedFirstOrderMatrixReification Δ (ofFirstOrder p) where
  formula := .quantified p
  roundTrip := rfl

def ScopedFirstOrderMatrixReification.neg
    (certificate : ScopedFirstOrderMatrixReification Δ raw) :
    ScopedFirstOrderMatrixReification Δ (smartNeg raw) where
  formula := .neg certificate.formula
  roundTrip := by simp [ofFirstOrderMatrixScoped, certificate.roundTrip]

def ScopedFirstOrderMatrixReification.disj
    (left : ScopedFirstOrderMatrixReification Δ p)
    (right : ScopedFirstOrderMatrixReification Δ q) :
    ScopedFirstOrderMatrixReification Δ (smartDisjScoped p q) where
  formula := .disj left.formula right.formula
  roundTrip := by
    simp [ofFirstOrderMatrixScoped, left.roundTrip, right.roundTrip]

def ofSecondOrder : SecondOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrder body)
  | .sometimes body => .quantified .sometimes (ofFirstOrder body)

def ofSecondMatrix : FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrderMatrix body)
  | .sometimes body => .quantified .sometimes (ofFirstOrderMatrix body)

def ofSecondMatrixScoped : FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrderMatrixScoped body)
  | .sometimes body => .quantified .sometimes (ofFirstOrderMatrixScoped body)

def ofThirdOrder : FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrix body)
  | .sometimes body => .quantified .sometimes (ofSecondMatrix body)

def ofThirdOrderScoped : FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrixScoped body)
  | .sometimes body => .quantified .sometimes (ofSecondMatrixScoped body)

def ofThirdOrderFormula : FirstOrderMatrix.ThirdOrderFormula Γ Δ → Raw Γ
  | .quantified p => ofThirdOrder p
  | .neg p => .neg (ofThirdOrderFormula p)
  | .disj p q => .disj (ofThirdOrderFormula p) (ofThirdOrderFormula q)

def ofThirdOrderFormulaScoped : FirstOrderMatrix.ThirdOrderFormula Γ Δ → Raw Γ
  | .quantified p => ofThirdOrderScoped p
  | .neg p => .neg (ofThirdOrderFormulaScoped p)
  | .disj p q =>
      .disj (ofThirdOrderFormulaScoped p) (ofThirdOrderFormulaScoped q)

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

theorem ofApparentAt_abstractRealOuter
    (depth : Nat)
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    ofApparentAt depth (Apparent.abstractRealOuter p) =
      abstractOuterAt depth (ofApparentAt depth p) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> simp [ofApparentAt,
      Apparent.abstractRealOuter, abstractOuterAt, abstractElementaryAt,
      boundIndex] <;> omega
  | bound boundVariable =>
      cases boundVariable with
      | zero => simp [ofApparentAt, Apparent.abstractRealOuter,
          abstractOuterAt, boundIndex]
      | succ predecessor =>
          have above : ¬ boundIndex predecessor + 1 + depth ≤ depth := by omega
          simp [ofApparentAt, Apparent.abstractRealOuter,
            abstractOuterAt, boundIndex, above]
          omega
  | neg proposition ih =>
      simp [ofApparentAt, Apparent.abstractRealOuter, abstractOuterAt, ih]
  | disj left right ihLeft ihRight =>
      simp [ofApparentAt, Apparent.abstractRealOuter, abstractOuterAt,
        ihLeft, ihRight]

theorem ofFirstOrderAt_abstractRealOuter
    (depth : Nat) (p : FirstOrder (.elementaryProposition :: Γ) Δ) :
    ofFirstOrderAt depth (FirstOrder.abstractRealOuter p) =
      abstractOuterAt depth (ofFirstOrderAt depth p) := by
  cases p <;>
    simp [FirstOrder.abstractRealOuter, ofFirstOrderAt, abstractOuterAt,
      ofApparentAt_abstractRealOuter]

/-- Canonical Raw opening is the exact image of `Apparent.openRealOuter`.
The apparent context has an inner binder plus the outer slot being opened. -/
theorem openOuter_ofApparent
    (p : Apparent Γ (.elementaryProposition :: .elementaryProposition :: Δ)) :
    openOuter (ofApparent p) = ofApparent (Apparent.openRealOuter p) := by
  induction p with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ predecessor =>
          cases predecessor with
          | zero => rfl
          | succ tail => rfl
  | neg proposition ih =>
      change Raw.neg (openOuter (ofApparent proposition)) =
        Raw.neg (ofApparent (Apparent.openRealOuter proposition))
      exact congrArg Raw.neg ih
  | disj left right ihLeft ihRight =>
      change Raw.disj (openOuter (ofApparent left)) (openOuter (ofApparent right)) =
        Raw.disj (ofApparent (Apparent.openRealOuter left))
          (ofApparent (Apparent.openRealOuter right))
      rw [ihLeft, ihRight]

/-- The canonical outer abstraction is beta-correct on the image of
`Apparent`: opening after abstraction recovers the original apparent term. -/
theorem openOuter_abstractOuter_ofApparent
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    openOuter (abstractOuter (ofApparent p)) = ofApparent p := by
  rw [← ofApparent_abstractRealOuter]
  rw [openOuter_ofApparent]
  simp

/-- Each source-labelled occurrence has an explicit beta law for the leading
real slot closed by `closeLeadingRaw`. -/
theorem openOuter_star_9_21_phi_x_closed_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_phi_x_closed_raw φ) = star_9_21_phi_x_raw φ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_psi_x_closed_raw
    (ψ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_psi_x_closed_raw ψ) = star_9_21_psi_x_raw ψ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_phi_y_closed_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_phi_y_closed_raw φ) = star_9_21_phi_y_raw φ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_psi_z_closed_raw
    (ψ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_psi_z_closed_raw ψ) = star_9_21_psi_z_raw ψ :=
  openOuter_abstractOuter_ofApparent _

/-- The `x` occurrence has no use of the innermost `y` slot after its leading
real variable is closed. -/
theorem star_9_21_phi_x_closed_unused_zero
    (φ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (star_9_21_phi_x_closed_raw φ) := by
  induction φ with
  | constant name => trivial
  | real realVariable =>
      change True
      trivial
  | bound boundVariable =>
      cases boundVariable
      simp [star_9_21_phi_x_closed_raw, closeLeadingRaw,
        star_9_21_phi_x_raw, ofApparent, abstractOuter, abstractOuterAt,
        Apparent.weakenReal, Apparent.renameReal,
        UnusedBoundAt, boundIndex]
      rename_i impossible
      exact nomatch impossible
  | neg proposition ih =>
      exact ih
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩

theorem star_9_21_psi_x_closed_unused_zero
    (ψ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (star_9_21_psi_x_closed_raw ψ) := by
  induction ψ with
  | constant name => trivial
  | real realVariable =>
      change True
      trivial
  | bound boundVariable =>
      cases boundVariable
      simp [star_9_21_psi_x_closed_raw, closeLeadingRaw,
        star_9_21_psi_x_raw, ofApparent, abstractOuter, abstractOuterAt,
        Apparent.weakenReal, Apparent.renameReal,
        UnusedBoundAt, boundIndex]
      rename_i impossible
      exact nomatch impossible
  | neg proposition ih => exact ih
  | disj left right ihLeft ihRight => exact ⟨ihLeft, ihRight⟩

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

/-- Scope-explicit Raw reading of printed line (4): the outer universal is
followed by the two existential binders generated by the higher ✱9·13
closure and the line-(3) matrix respectively. -/
def star_9_21_line4_explicit_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (ofFirstOrderMatrix (FirstOrderMatrix.abstractRealOuter
      (PM.Architecture.FirstOrderPrerequisites.star_9_21_line3_matrix φ ψ))))

theorem star_9_21_line4_raw_explicit
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_line4_raw φ ψ = star_9_21_line4_explicit_raw φ ψ := rfl

/-- Raw implication, used only to spell out the source-labelled displayed
lines of ✱9·21. -/
def rawImp (p q : Raw Γ) : Raw Γ := .disj (.neg p) q

/-- Matrix-level spelling of line (4), with the binders `z`, `x`, and `y`
made explicit in their printed order. -/
def star_9_21_line4_named_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes (.quantified .sometimes
    (rawImp (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ))
      (rawImp (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ)))))

/-- Printed line (5) of ✱9·21.  Its source operation is ✱9·06: the final
existential is transferred from the implication's antecedent scope into the
consequent. -/
def star_9_21_line5_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (rawImp (dropUnusedBound
      (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ)))
      (.quantified .sometimes
        (rawImp (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ)))))

/-- Printed line (6) of ✱9·21, after the displayed implication abbreviation
and ✱9·08 scope transformation. -/
def star_9_21_line6_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.quantified .sometimes
      (.neg (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ))))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg (star_9_21_phi_y_closed_raw φ)) (star_9_21_psi_z_closed_raw ψ))))

/-- Printed line (7) retains the same visible binder pattern as line (6);
the cited second ✱9·08 records the final scope normalization before ✱1·01. -/
def star_9_21_line7_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  star_9_21_line6_raw φ ψ

theorem star_9_21_line4_raw_named
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_line4_raw φ ψ = star_9_21_line4_named_raw φ ψ := by
  change Raw.quantified .always (Raw.quantified .sometimes (Raw.quantified .sometimes
    (ofApparent (Apparent.abstractRealOuter
      (PM.Architecture.FirstOrderPrerequisites.matrixImp
        (PM.Architecture.FirstOrderPrerequisites.matrixImp _ _)
        (PM.Architecture.FirstOrderPrerequisites.matrixImp _ _)))))) = _
  simp only [PM.Architecture.FirstOrderPrerequisites.matrixImp,
    Apparent.abstractRealOuter, ofApparent]
  simp only [star_9_21_line4_named_raw, rawImp,
    star_9_21_phi_x_closed_raw, star_9_21_psi_x_closed_raw,
    star_9_21_phi_y_closed_raw, star_9_21_psi_z_closed_raw,
    closeLeadingRaw, star_9_21_phi_x_raw, star_9_21_psi_x_raw,
    star_9_21_phi_y_raw, star_9_21_psi_z_raw]
  rw [ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter]



end PM.Architecture.CanonicalOrderedAdapters
