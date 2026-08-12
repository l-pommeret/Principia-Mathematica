import Principia.Syntax.Ordered

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
  smartDisjRight (smartNeg (.quantified .always matrix)) conclusion

def line2Normal (matrix conclusion : Raw Γ) : Raw Γ :=
  .quantified .sometimes (smartDisjRight (smartNeg matrix) conclusion)

/- Exact experimental witness: ✱9·02 turns the negated universal into an
existential, and ✱9·03 pushes the remaining disjunction below that binder.
Both printed lines therefore package the same raw canonical AST. -/
theorem star_9_03_02_line1_line2 (matrix conclusion : Raw Γ) :
    line1Redex matrix conclusion = line2Normal matrix conclusion := by
  rfl

theorem packed_star_9_03_02 (matrix conclusion : Raw Γ) :
    pack (line1Redex matrix conclusion) = pack (line2Normal matrix conclusion) := by
  rw [star_9_03_02_line1_line2]

end PM.Experimental.CanonicalOrderedFormula
