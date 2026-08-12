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
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

def assignedOrder : Raw Γ → Nat
  | .elementary _ => 0
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
  | left@(.quantified .always _), right@(.quantified .sometimes _) =>
      smartDisjRight left right
  | left@(.quantified .sometimes _), right@(.quantified .always _) =>
      smartDisjLeft left right
  | left@(.quantified _ _), right => smartDisjRight left right
  | left, right@(.quantified _ _) => smartDisjLeft left right
  | left, right => .disj left right

def smartImp (left right : Raw Γ) : Raw Γ := smartDisj (smartNeg left) right

/- Conservative raw embeddings of the three constructors represented by the
current indexed syntax.  Connective nodes retain their existing structure;
only the explicit order index is forgotten. -/
def ofApparent : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound _ => .elementary (.constant "<apparent-bound>")
  | .neg p => .neg (ofApparent p)
  | .disj p q => .disj (ofApparent p) (ofApparent q)

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
def line1Redex (matrix conclusion : Raw Γ) : Raw Γ :=
  .quantified .always (smartDisjRight (smartNeg matrix) conclusion)

def line2Normal (matrix conclusion : Raw Γ) : Raw Γ :=
  smartDisjRight (smartNeg (.quantified .sometimes matrix)) conclusion

/- Exact experimental witness: ✱9·02 turns the negated existential antecedent
into a universal, and ✱9·03 pushes the remaining disjunction below that binder.
Both printed lines therefore package the same raw canonical AST. -/
theorem star_9_03_02_line1_line2 (matrix conclusion : Raw Γ) :
    line1Redex matrix conclusion = line2Normal matrix conclusion := by
  rfl

theorem packed_star_9_03_02 (matrix conclusion : Raw Γ) :
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
theorem assertion_star_9_03_02 {matrix conclusion : Raw Γ} :
    Assertion (line1Redex matrix conclusion) →
      Assertion (line2Normal matrix conclusion) :=
  Assertion.convert (star_9_03_02_line1_line2 matrix conclusion)

/-- Conservation theorem: every canonical assertion exposes the precise
indexed kernel assertion from which it originated. -/
theorem assertion_conservative {p : Raw Γ} (proof : Assertion p) :
    ∃ (order : Nat) (q : OrderedFormula Γ order),
      OrderedAssertion q ∧ ofOrdered q = p :=
  proof

end PM.Experimental.CanonicalOrderedFormula
