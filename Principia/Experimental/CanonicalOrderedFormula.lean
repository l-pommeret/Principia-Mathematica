import Principia.Architecture.FirstOrderPrerequisites

namespace PM.Experimental.CanonicalOrderedFormula

/-!
Experimental canonical representation for the ✱9 migration.

Unlike `OrderedFormula`, `Raw` is not indexed by an order.  Smart constructors
perform the definitional reductions ✱9·03–·08 before a formula is packaged
with its computed assigned order.  This makes an order-changing printed
reduction an ordinary equality of canonical syntax rather than an impossible
equality between distinct indexed types.
-/

inductive Quantifier where
  | always
  | sometimes
  deriving DecidableEq, Repr

inductive Raw : RealContext → Type where
  | elementary : Elementary Γ → Raw Γ
  | bound : Nat → Raw Γ
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

/-- Elementary matrices contain real and apparent-variable atoms but no
quantifier.  Keeping this fragment separate makes the ✱9·03–·08 smart
reductions total rather than guarded by a run-time order test. -/
inductive MatrixRaw : RealContext → Type where
  | elementary : Elementary Γ → MatrixRaw Γ
  | bound : Nat → MatrixRaw Γ
  | neg : MatrixRaw Γ → MatrixRaw Γ
  | disj : MatrixRaw Γ → MatrixRaw Γ → MatrixRaw Γ
  deriving DecidableEq, Repr

def MatrixRaw.toRaw : MatrixRaw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => .bound index
  | .neg p => .neg p.toRaw
  | .disj p q => .disj p.toRaw q.toRaw

/-- Open the outer one of two apparent variables as a newly leading real
variable. Bound zero is the pre-existing inner variable; bound one is opened;
deeper indices lose exactly that outer slot. -/
def openOuter : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary p => .elementary
      (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  | .bound 0 => .bound 0
  | .bound 1 => .elementary (.var .zero)
  | .bound (index + 2) => .bound (index + 1)
  | .quantified quantifier body => .quantified quantifier (openOuter body)
  | .neg p => .neg (openOuter p)
  | .disj p q => .disj (openOuter p) (openOuter q)

def MatrixRaw.smartNeg : MatrixRaw Γ → MatrixRaw Γ
  | matrix => .neg matrix

/- Repeated apparent variables of the same elementary type remain at the same
first assigned order. Binder depth is not proposition type order. -/
def assignedOrder : Raw Γ → Nat
  | .elementary _ => 0
  | .bound _ => 0
  | .quantified _ body => max 1 (assignedOrder body)
  | .neg proposition => assignedOrder proposition
  | .disj left right => max (assignedOrder left) (assignedOrder right)

abbrev Packed (Γ : RealContext) := Σ order : Nat, {p : Raw Γ // assignedOrder p = order}

def pack (p : Raw Γ) : Packed Γ := ⟨assignedOrder p, p, rfl⟩

/- Smart negation implements ✱9·01/·02 at the raw canonical level. -/
def smartNeg : Raw Γ → Raw Γ
  | .quantified .always body => .quantified .sometimes (smartNeg body)
  | .quantified .sometimes body => .quantified .always (smartNeg body)
  | proposition => .neg proposition

/- Push a disjunction beneath a leading quantifier.  These two operations are
the canonical forms of ✱9·03/05 and ✱9·04/06 respectively. -/
def smartDisjRight : Raw Γ → Raw Γ → Raw Γ
  | .quantified quantifier body, right =>
      .quantified quantifier (smartDisjRight body right)
  | left, right => .disj left right

def smartDisjLeft : Raw Γ → Raw Γ → Raw Γ
  | left, .quantified quantifier body =>
      .quantified quantifier (smartDisjLeft left body)
  | left, right => .disj left right

/- ✱9·07/·08: when both sides already carry a leading quantifier, retain the
printed outer binder and reduce the inner disjunction recursively. -/
def smartDisj : Raw Γ → Raw Γ → Raw Γ
  | .quantified .always left, .quantified .sometimes right =>
      .quantified .always (.quantified .sometimes (smartDisj left right))
  | .quantified .sometimes left, .quantified .always right =>
      .quantified .always (.quantified .sometimes (smartDisj left right))
  | .quantified quantifier left, right =>
      .quantified quantifier (smartDisj left right)
  | left, .quantified quantifier right =>
      .quantified quantifier (smartDisj left right)
  | left, right => .disj left right

def smartImp (left right : Raw Γ) : Raw Γ := smartDisj (smartNeg left) right

/-!
## Scope-aware successor normalizer

This second normalizer is kept separate while the earlier experimental
certificates are migrated.  Its explicit fuel is bounded by the syntax size;
recursive calls consume a leading quantifier and therefore need no unsafe or
opaque termination argument.
-/

def shiftBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .bound index => if cutoff ≤ index then .bound (index + 1) else .bound index
  | .quantified quantifier body =>
      .quantified quantifier (shiftBoundAt (cutoff + 1) body)
  | .neg p => .neg (shiftBoundAt cutoff p)
  | .disj p q => .disj (shiftBoundAt cutoff p) (shiftBoundAt cutoff q)

def weakenBound (p : Raw Γ) : Raw Γ := shiftBoundAt 0 p

def smartDisjScopedAux : Nat → Raw Γ → Raw Γ → Raw Γ
  | 0, left, right => .disj left right
  | fuel + 1, .quantified .always left, .quantified .sometimes right =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux fuel (weakenBound left) right))
  | fuel + 1, .quantified .sometimes left, .quantified .always right =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux fuel (weakenBound left) right))
  | fuel + 1, .quantified quantifier left, right =>
      .quantified quantifier (smartDisjScopedAux fuel left (weakenBound right))
  | fuel + 1, left, .quantified quantifier right =>
      .quantified quantifier (smartDisjScopedAux fuel (weakenBound left) right)
  | _ + 1, left, right => .disj left right

def rawSize : Raw Γ → Nat
  | .elementary _ | .bound _ => 1
  | .quantified _ body | .neg body => rawSize body + 1
  | .disj left right => rawSize left + rawSize right + 1

def smartDisjScoped (left right : Raw Γ) : Raw Γ :=
  smartDisjScopedAux (rawSize left + rawSize right) left right

@[simp] theorem shiftBoundAt_elementary (p : Elementary Γ) :
    shiftBoundAt cutoff (.elementary p) = .elementary p := rfl

@[simp] theorem shiftBoundAt_quantified (quantifier) (body : Raw Γ) :
    shiftBoundAt cutoff (.quantified quantifier body) =
      .quantified quantifier (shiftBoundAt (cutoff + 1) body) := rfl

@[simp] theorem smartDisjScoped_matrix
    (left right : MatrixRaw Γ) :
    smartDisjScoped left.toRaw right.toRaw = .disj left.toRaw right.toRaw := by
  cases left <;> cases right <;>
    rfl

/- Conservative raw embeddings of the three constructors represented by the
current indexed syntax.  Connective nodes retain their existing structure;
only the explicit order index is forgotten. -/
def boundIndex : BoundVar Δ .elementaryProposition → Nat
  | .zero => 0
  | .succ v => boundIndex v + 1

def ofApparent : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v)
  | .neg p => .neg (ofApparent p)
  | .disj p q => .disj (ofApparent p) (ofApparent q)

@[simp] theorem boundIndex_succ (v : BoundVar Δ .elementaryProposition) :
    boundIndex (BoundVar.succ (σ := .elementaryProposition) v) =
      boundIndex v + 1 := rfl

/-- Raw weakening agrees exactly with capture-free apparent-variable
weakening.  This is the scope law used whenever normalization moves a matrix
beneath a quantifier introduced by the other disjunct. -/
@[simp] theorem weakenBound_ofApparent (p : Apparent Γ Δ) :
    weakenBound (ofApparent p) =
      ofApparent (Apparent.weaken (τ := .elementaryProposition) p) := by
  induction p with
  | constant name => rfl
  | real v => rfl
  | bound v => rfl
  | neg p ih => exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj (weakenBound (ofApparent p))
        (weakenBound (ofApparent q)) = _
      rw [ihp, ihq]
      rfl

@[simp] theorem ofApparent_bound_zero {Γ} :
    ofApparent (Apparent.bound (.zero : BoundVar
      (.elementaryProposition :: Δ) .elementaryProposition) :
        Apparent Γ (.elementaryProposition :: Δ)) = .bound 0 := rfl

@[simp] theorem ofApparent_bound_succ {Γ}
    (v : BoundVar Δ .elementaryProposition) :
    ofApparent (Apparent.bound (.succ v) :
      Apparent Γ (.elementaryProposition :: Δ)) = .bound (boundIndex v + 1) := rfl

theorem raw_bound_injective {left right : Nat} :
    (Raw.bound left : Raw Γ) = .bound right → left = right := by
  intro equality
  injection equality

theorem boundIndex_openRealOuter
    (v : BoundVar (.elementaryProposition :: .elementaryProposition :: Δ)
      .elementaryProposition) :
    openOuter (.bound (boundIndex v) : Raw Γ) =
      ofApparent (Apparent.openRealOuter (Apparent.bound v) :
        Apparent (.elementaryProposition :: Γ)
          (.elementaryProposition :: Δ)) := by
  cases v with
  | zero => rfl
  | succ v =>
      cases v with
      | zero => rfl
      | succ predecessor => rfl

/-- The raw scope operation is exactly the embedding of the canonical
`Apparent.openRealOuter`; no semantic interpretation or assertion transport
is involved. -/
theorem openOuter_ofApparent
    (p : Apparent Γ
      (.elementaryProposition :: .elementaryProposition :: Δ)) :
    openOuter (ofApparent p) = ofApparent (Apparent.openRealOuter p) := by
  induction p with
  | constant name => rfl
  | real v => rfl
  | bound v => exact boundIndex_openRealOuter v
  | neg p ih => simp [ofApparent, openOuter, Apparent.openRealOuter, ih]
  | disj p q ihp ihq =>
      simp [ofApparent, openOuter, Apparent.openRealOuter, ihp, ihq]

def matrixOfApparent : Apparent Γ Δ → MatrixRaw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v)
  | .neg p => .neg (matrixOfApparent p)
  | .disj p q => .disj (matrixOfApparent p) (matrixOfApparent q)

@[simp] theorem matrixOfApparent_toRaw (p : Apparent Γ Δ) :
    (matrixOfApparent p).toRaw = ofApparent p := by
  induction p <;> simp [matrixOfApparent, MatrixRaw.toRaw, ofApparent, *]

@[simp] theorem smartDisj_ofApparent (p : Apparent Γ Δ)
    (q : Apparent Γ Ξ) :
    smartDisj (ofApparent p) (ofApparent q) =
      .disj (ofApparent p) (ofApparent q) := by
  cases p <;> cases q <;> simp [ofApparent, smartDisj]

@[simp] theorem ofApparent_disj_smart (p : Apparent Γ Δ)
    (q : Apparent Γ Δ) :
    ofApparent (p ∨ₐ q) = smartDisj (ofApparent p) (ofApparent q) := by
  simp [ofApparent]

@[simp] theorem ofApparent_neg (p : Apparent Γ Δ) :
    ofApparent (∼ₐ p) = .neg (ofApparent p) := rfl

@[simp] theorem smartNeg_ofApparent (p : Apparent Γ Δ) :
    smartNeg (ofApparent p) = .neg (ofApparent p) := by
  cases p <;> rfl

def ofFirstOrder : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparent body)
  | .sometimes body => .quantified .sometimes (ofApparent body)

/-- Canonical normalization of the explicit same-order first-order matrix
language.  It applies exactly the already-audited smart negation and
disjunction reductions; no assertion is introduced. -/
def normalizeFirstOrderMatrix : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified proposition => ofFirstOrder proposition
  | .neg matrix => smartNeg (normalizeFirstOrderMatrix matrix)
  | .disj left right => smartDisj
      (normalizeFirstOrderMatrix left) (normalizeFirstOrderMatrix right)

/-- Capture-safe successor normalizer.  Unlike the historical experimental
normalizer above, this version shifts the opposite disjunct whenever a
quantifier is crossed. -/
def normalizeFirstOrderMatrixScoped : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified proposition => ofFirstOrder proposition
  | .neg matrix => smartNeg (normalizeFirstOrderMatrixScoped matrix)
  | .disj left right => smartDisjScoped
      (normalizeFirstOrderMatrixScoped left)
      (normalizeFirstOrderMatrixScoped right)

structure ScopedCertifiedFirstOrderMatrix
    (Δ : BoundContext) (raw : Raw Γ) where
  formula : FirstOrderMatrix Γ Δ
  roundTrip : normalizeFirstOrderMatrixScoped formula = raw

def certifyFirstOrderScoped (proposition : FirstOrder Γ Δ) :
    ScopedCertifiedFirstOrderMatrix Δ (ofFirstOrder proposition) where
  formula := .quantified proposition
  roundTrip := rfl

def ScopedCertifiedFirstOrderMatrix.neg
    (certificate : ScopedCertifiedFirstOrderMatrix Δ raw) :
    ScopedCertifiedFirstOrderMatrix Δ (smartNeg raw) where
  formula := .neg certificate.formula
  roundTrip := by simp [normalizeFirstOrderMatrixScoped, certificate.roundTrip]

def ScopedCertifiedFirstOrderMatrix.disj
    (left : ScopedCertifiedFirstOrderMatrix Δ p)
    (right : ScopedCertifiedFirstOrderMatrix Δ q) :
    ScopedCertifiedFirstOrderMatrix Δ (smartDisjScoped p q) where
  formula := .disj left.formula right.formula
  roundTrip := by
    simp [normalizeFirstOrderMatrixScoped, left.roundTrip, right.roundTrip]

def ScopedCertifiedFirstOrderMatrix.imp
    (left : ScopedCertifiedFirstOrderMatrix Δ p)
    (right : ScopedCertifiedFirstOrderMatrix Δ q) :
    ScopedCertifiedFirstOrderMatrix Δ
      (smartDisjScoped (smartNeg p) q) :=
  left.neg.disj right

/-- A range certificate for conservative reification.  There is deliberately
no total `Raw → FirstOrderMatrix`: callers must exhibit syntax whose canonical
normalization is the requested raw formula. -/
structure CertifiedFirstOrderMatrix (Δ : BoundContext) (raw : Raw Γ) where
  formula : FirstOrderMatrix Γ Δ
  roundTrip : normalizeFirstOrderMatrix formula = raw

def certifyFirstOrder (proposition : FirstOrder Γ Δ) :
    CertifiedFirstOrderMatrix Δ (ofFirstOrder proposition) where
  formula := .quantified proposition
  roundTrip := rfl

def CertifiedFirstOrderMatrix.neg
    (certificate : CertifiedFirstOrderMatrix Δ raw) :
    CertifiedFirstOrderMatrix Δ (smartNeg raw) where
  formula := .neg certificate.formula
  roundTrip := by simp [normalizeFirstOrderMatrix, certificate.roundTrip]

def CertifiedFirstOrderMatrix.disj
    (left : CertifiedFirstOrderMatrix Δ p)
    (right : CertifiedFirstOrderMatrix Δ q) :
    CertifiedFirstOrderMatrix Δ (smartDisj p q) where
  formula := .disj left.formula right.formula
  roundTrip := by simp [normalizeFirstOrderMatrix, left.roundTrip, right.roundTrip]

def CertifiedFirstOrderMatrix.imp
    (left : CertifiedFirstOrderMatrix Δ p)
    (right : CertifiedFirstOrderMatrix Δ q) :
    CertifiedFirstOrderMatrix Δ (smartImp p q) :=
  left.neg.disj right

theorem certified_roundTrip
    (certificate : CertifiedFirstOrderMatrix Δ raw) :
    normalizeFirstOrderMatrix certificate.formula = raw :=
  certificate.roundTrip

def ofSecondOrder : SecondOrder Γ [] → Raw Γ
  | .always body => .quantified .always (ofFirstOrder body)
  | .sometimes body => .quantified .sometimes (ofFirstOrder body)

def ofSecondOrderMatrix : FirstOrderMatrix.Quantified Γ [] → Raw Γ
  | .always body => .quantified .always (normalizeFirstOrderMatrix body)
  | .sometimes body => .quantified .sometimes (normalizeFirstOrderMatrix body)

def ofThirdOrderMatrix : FirstOrderMatrix.ThirdOrder Γ [] → Raw Γ
  | .always (.always body) =>
      .quantified .always (.quantified .always (normalizeFirstOrderMatrix body))
  | .always (.sometimes body) =>
      .quantified .always (.quantified .sometimes (normalizeFirstOrderMatrix body))
  | .sometimes (.always body) =>
      .quantified .sometimes (.quantified .always (normalizeFirstOrderMatrix body))
  | .sometimes (.sometimes body) =>
      .quantified .sometimes (.quantified .sometimes (normalizeFirstOrderMatrix body))

def ofThirdOrderFormula : FirstOrderMatrix.ThirdOrderFormula Γ [] → Raw Γ
  | .quantified p => ofThirdOrderMatrix p
  | .neg p => .neg (ofThirdOrderFormula p)
  | .disj p q => .disj (ofThirdOrderFormula p) (ofThirdOrderFormula q)

def ofOrdered : OrderedFormula Γ order → Raw Γ
  | .elementary p => .elementary p
  | .firstOrder p => ofFirstOrder p
  | .firstOrderMatrix p => normalizeFirstOrderMatrix p
  | .secondOrder p => ofSecondOrder p
  | .secondOrderMatrix p => ofSecondOrderMatrix p
  | .thirdOrderMatrix p => ofThirdOrderMatrix p
  | .thirdOrderFormula p => ofThirdOrderFormula p
  | .neg p => .neg (ofOrdered p)
  | .disj _ p q => .disj (ofOrdered p) (ofOrdered q)

/- The canonical ✱9·03·02 redex used between lines (1) and (2) of ✱9·31. -/
def line1Redex (matrix : MatrixRaw Γ) (conclusion : Raw Γ) : Raw Γ :=
  .quantified .always (smartDisj matrix.smartNeg.toRaw conclusion)

def line2Normal (matrix : MatrixRaw Γ) (conclusion : Raw Γ) : Raw Γ :=
  smartDisj (.quantified .always matrix.smartNeg.toRaw) conclusion

/- Exact experimental witness: ✱9·02 turns the negated existential antecedent
into a universal, and ✱9·03 pushes the remaining disjunction below that binder.
Both printed lines therefore package the same raw canonical AST. -/
theorem star_9_03_02_line1_line2 (matrix : MatrixRaw Γ) (conclusion : Raw Γ) :
    line1Redex matrix conclusion = line2Normal matrix conclusion := by
  cases conclusion with
  | quantified quantifier body =>
      cases quantifier <;>
        simp [line1Redex, line2Normal, MatrixRaw.smartNeg, MatrixRaw.toRaw, smartDisj]
  | elementary p => simp [line1Redex, line2Normal, MatrixRaw.smartNeg, MatrixRaw.toRaw, smartDisj]
  | bound index => simp [line1Redex, line2Normal, MatrixRaw.smartNeg, MatrixRaw.toRaw, smartDisj]
  | neg p => simp [line1Redex, line2Normal, MatrixRaw.smartNeg, MatrixRaw.toRaw, smartDisj]
  | disj p q => simp [line1Redex, line2Normal, MatrixRaw.smartNeg, MatrixRaw.toRaw, smartDisj]

theorem packed_star_9_03_02 (matrix : MatrixRaw Γ) (conclusion : Raw Γ) :
    pack (line1Redex matrix conclusion) = pack (line2Normal matrix conclusion) := by
  rw [star_9_03_02_line1_line2]

/-!
## Conservative judgement image

An experimental canonical assertion is inhabited only when an assertion in
the current indexed kernel maps to that exact raw AST.  This definition adds
no primitive proposition and no inference constructor; it is merely the image
of the existing judgement under `ofOrdered`.
-/

open PM.Architecture.FirstOrderPrerequisites

def Assertion (p : Raw Γ) : Prop :=
  ∃ (order : Nat) (q : OrderedFormula Γ order),
    OrderedAssertion q ∧ ofOrdered q = p

theorem assertion_of_ordered {q : OrderedFormula Γ order}
    (proof : OrderedAssertion q) : Assertion (ofOrdered q) :=
  ⟨order, q, proof, rfl⟩

theorem Assertion.convert {p q : Raw Γ} (equality : p = q) :
    Assertion p → Assertion q := by
  intro proof
  cases equality
  exact proof

/-- Judgement-level ✱9·03·02 transport, conservative by construction: the
underlying indexed proof witness is unchanged and only its canonical raw
presentation is rewritten. -/
theorem assertion_star_9_03_02 {matrix : MatrixRaw Γ} {conclusion : Raw Γ} :
    Assertion (line1Redex matrix conclusion) →
      Assertion (line2Normal matrix conclusion) :=
  Assertion.convert (star_9_03_02_line1_line2 matrix conclusion)

/-- Conservation theorem: every canonical assertion exposes the precise
indexed kernel assertion from which it originated. -/
theorem assertion_conservative {p : Raw Γ} (proof : Assertion p) :
    ∃ (order : Nat) (q : OrderedFormula Γ order),
      OrderedAssertion q ∧ ofOrdered q = p :=
  proof

/-!
## The first closure in ✱9·31

This is the exact kernel witness obtained by applying the first-order instance
of ✱9·13 to primitive ✱9·11.  It closes one of the two displayed real values;
no normalization or new assertion principle occurs here.
-/

def star_9_31_primitive_payload (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: .elementaryProposition :: Γ) [] :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  let φx := Apparent.atReal lifted .zero
  let φy := Apparent.atReal lifted (.succ .zero)
  let conclusion := FirstOrder.weakenReal
    (FirstOrder.weakenReal (FirstOrder.sometimes φ))
  FirstOrder.impElementaryToFirst (φx ∨ₚ φy) conclusion

def star_9_31_line1_matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.abstractRealOuter (star_9_31_primitive_payload φ)

theorem star_9_31_line1_ordered (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion
      (firstOrderToSecondAll (star_9_31_line1_matrix φ)) := by
  apply OrderedAssertion.star_9_13_first (star_9_31_line1_matrix φ)
  simpa [star_9_31_line1_matrix, star_9_31_primitive_payload,
    star_9_11_target] using OrderedAssertion.star_9_11 φ

theorem star_9_31_line1_canonical (φ : Apparent Γ [.elementaryProposition]) :
    Assertion (ofOrdered
      (firstOrderToSecondAll (star_9_31_line1_matrix φ))) :=
  assertion_of_ordered (star_9_31_line1_ordered φ)

def star_9_31_antecedent (φ : Apparent Γ [.elementaryProposition]) :
    Elementary (.elementaryProposition :: .elementaryProposition :: Γ) :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  Apparent.atReal lifted .zero ∨ₚ Apparent.atReal lifted (.succ .zero)

def star_9_31_canonical_matrix (φ : Apparent Γ [.elementaryProposition]) :
    MatrixRaw (.elementaryProposition :: Γ) :=
  matrixOfApparent (Apparent.abstractRealOuter
    (Apparent.ofElementary (star_9_31_antecedent φ) :
      Apparent (.elementaryProposition :: .elementaryProposition :: Γ)
        [.elementaryProposition]))

def star_9_31_canonical_conclusion (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .quantified .sometimes (ofApparent (Apparent.abstractRealOuter
    (Apparent.weakenReal (Apparent.weakenReal φ))))

theorem ofApparent_abstractRealOuter_weaken_twice
    (φ : Apparent Γ [.elementaryProposition]) :
    ofApparent (Apparent.abstractRealOuter
      (Apparent.weakenReal
        (Apparent.weakenReal φ : Apparent
          (.elementaryProposition :: Γ) [.elementaryProposition]))) =
    ofApparent (Apparent.rename Apparent.innerVariableRenaming
      (Apparent.weakenReal φ : Apparent
        (.elementaryProposition :: Γ) [.elementaryProposition])) := by
  exact congrArg ofApparent
    (Apparent.abstractRealOuter_weakenReal
      (φ := (Apparent.weakenReal φ : Apparent
        (.elementaryProposition :: Γ) [.elementaryProposition])))

@[simp] theorem ofApparent_abstractRealOuter_ofElementary_neg
    (p : Elementary (.elementaryProposition :: Γ)) :
    ofApparent (Apparent.abstractRealOuter
      (Apparent.ofElementary (∼ₚ p) : Apparent
        (.elementaryProposition :: Γ) [.elementaryProposition])) =
    .neg (ofApparent (Apparent.abstractRealOuter
      (Apparent.ofElementary p : Apparent
        (.elementaryProposition :: Γ) [.elementaryProposition]))) := by
  rfl

theorem star_9_31_line1_identification
    (φ : Apparent Γ [.elementaryProposition]) :
    ofOrdered (firstOrderToSecondAll (star_9_31_line1_matrix φ)) =
      line1Redex (star_9_31_canonical_matrix φ)
        (star_9_31_canonical_conclusion φ) := by
  rw [firstOrderToSecondAll_reduction]
  simp [star_9_31_line1_matrix, star_9_31_primitive_payload,
    star_9_31_antecedent, star_9_31_canonical_matrix,
    star_9_31_canonical_conclusion, OrderedFormula.alwaysFirstOrder,
    FirstOrder.abstractRealOuter, FirstOrder.impElementaryToFirst,
    FirstOrder.disjElementaryLeft, FirstOrder.weakenReal, Apparent.weakenReal,
    ofOrdered, ofSecondOrder, ofFirstOrder,
    line1Redex, smartDisj, MatrixRaw.smartNeg, MatrixRaw.toRaw,
    matrixOfApparent_toRaw, Apparent.abstractRealOuter, Apparent.ofElementary,
    ofApparent_abstractRealOuter_weaken_twice,
    ofApparent_abstractRealOuter_ofElementary_neg, smartDisj_ofApparent]

theorem star_9_31_line2_canonical (φ : Apparent Γ [.elementaryProposition]) :
    Assertion (line2Normal (star_9_31_canonical_matrix φ)
      (star_9_31_canonical_conclusion φ)) := by
  apply assertion_star_9_03_02
  exact Assertion.convert (star_9_31_line1_identification φ)
    (star_9_31_line1_canonical φ)

theorem assignedOrder_matrix_toRaw (matrix : MatrixRaw Γ) :
    assignedOrder matrix.toRaw = 0 := by
  induction matrix <;> simp [MatrixRaw.toRaw, assignedOrder, *]

theorem assignedOrder_ofApparent (matrix : Apparent Γ Δ) :
    assignedOrder (ofApparent matrix) = 0 := by
  induction matrix <;> simp [ofApparent, assignedOrder, *]

/-- The normalized line (2) of ✱9·31 is first-order even though its canonical
AST contains two apparent binders.  This is the bridge needed before the
second printed application of ✱9·13. -/
theorem star_9_31_line2_assignedOrder
    (φ : Apparent Γ [.elementaryProposition]) :
    assignedOrder (line2Normal (star_9_31_canonical_matrix φ)
      (star_9_31_canonical_conclusion φ)) = 1 := by
  rw [← star_9_03_02_line1_line2]
  rw [← star_9_31_line1_identification]
  rw [firstOrderToSecondAll_reduction]
  simp [OrderedFormula.alwaysFirstOrder, ofOrdered, ofSecondOrder, ofFirstOrder,
    assignedOrder, assignedOrder_ofApparent, star_9_31_line1_matrix,
    star_9_31_primitive_payload, FirstOrder.abstractRealOuter,
    FirstOrder.impElementaryToFirst, FirstOrder.disjElementaryLeft,
    FirstOrder.weakenReal]

def star_9_31_line2_antecedent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes (Apparent.abstractRealOuter
    (Apparent.ofElementary (star_9_31_antecedent φ) : Apparent
      (.elementaryProposition :: .elementaryProposition :: Γ)
        [.elementaryProposition]))

def star_9_31_line2_consequent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes (Apparent.abstractRealOuter
    (Apparent.weakenReal (Apparent.weakenReal φ)))

/-- Certified reification of normalized line (2) into the explicit
same-first-order matrix language.  The certificate retains its round-trip
proof; it does not assert the formula. -/
def star_9_31_line2_reification (φ : Apparent Γ [.elementaryProposition]) :
    CertifiedFirstOrderMatrix [.elementaryProposition]
      (line2Normal (star_9_31_canonical_matrix φ)
        (star_9_31_canonical_conclusion φ)) := by
  let certificate := (certifyFirstOrder (star_9_31_line2_antecedent φ)).imp
    (certifyFirstOrder (star_9_31_line2_consequent φ))
  refine ⟨certificate.formula, ?_⟩
  rw [certificate.roundTrip]
  simp [star_9_31_line2_antecedent, star_9_31_line2_consequent,
    star_9_31_canonical_matrix, star_9_31_canonical_conclusion,
    line2Normal, smartImp, smartNeg, MatrixRaw.smartNeg, MatrixRaw.toRaw,
    matrixOfApparent_toRaw, ofFirstOrder, star_9_31_antecedent]

/-- The displayed value of normalized line (2), with its remaining apparent
slot instantiated at the leading real variable.  Instantiation is performed
by the existing capture-safe matrix operation before normalization. -/
def star_9_31_line2_open_formula (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix (.elementaryProposition :: Γ) [] :=
  FirstOrderMatrix.atReal (star_9_31_line2_reification φ).formula .zero

/-- Scope-aware range certificate for the opened line (2).  Its target is
definitionally the normalization of the exact instantiated syntax; no
judgement transport or assertion is bundled into this witness. -/
def star_9_31_line2_open_reification
    (φ : Apparent Γ [.elementaryProposition]) :
    ScopedCertifiedFirstOrderMatrix []
      (normalizeFirstOrderMatrixScoped (star_9_31_line2_open_formula φ)) where
  formula := star_9_31_line2_open_formula φ
  roundTrip := rfl

end PM.Experimental.CanonicalOrderedFormula
