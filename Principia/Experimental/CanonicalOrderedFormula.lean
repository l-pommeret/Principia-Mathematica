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

def MatrixRaw.smartNeg : MatrixRaw Γ → MatrixRaw Γ
  | matrix => .neg matrix

def assignedOrder : Raw Γ → Nat
  | .elementary _ => 0
  | .bound _ => 0
  | .quantified _ body => assignedOrder body + 1
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

def matrixOfApparent : Apparent Γ Δ → MatrixRaw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v)
  | .neg p => .neg (matrixOfApparent p)
  | .disj p q => .disj (matrixOfApparent p) (matrixOfApparent q)

@[simp] theorem matrixOfApparent_toRaw (p : Apparent Γ Δ) :
    (matrixOfApparent p).toRaw = ofApparent p := by
  induction p <;> simp [matrixOfApparent, MatrixRaw.toRaw, ofApparent, *]

def ofFirstOrder : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparent body)
  | .sometimes body => .quantified .sometimes (ofApparent body)

def ofSecondOrder : SecondOrder Γ [] → Raw Γ
  | .always body => .quantified .always (ofFirstOrder body)
  | .sometimes body => .quantified .sometimes (ofFirstOrder body)

def ofOrdered : OrderedFormula Γ order → Raw Γ
  | .elementary p => .elementary p
  | .firstOrder p => ofFirstOrder p
  | .secondOrder p => ofSecondOrder p
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

end PM.Experimental.CanonicalOrderedFormula
