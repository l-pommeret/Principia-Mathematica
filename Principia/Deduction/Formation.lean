import Principia.Syntax.Formula
import Principia.Syntax.Printed

namespace PM

/-- Explicit evidence that an elementary expression is licensed by PM's
primitive formation propositions.

Although `Elementary Γ` is intrinsically typed, this second judgement preserves
the historical distinction between formation in the empty context (✱1·71) and
identification of the real-variable type in a nonempty context (✱1·72). -/
inductive Formation : {Γ : RealContext} → Elementary Γ → Prop where
  /-- Carrier base case for an elementary constant.

  This is internal evidence for the intrinsically typed syntax, not an
  unnumbered primitive proposition or formation rule of PM. -/
  | constant (name : String) : Formation (.constant name)
  /-- Carrier base case for a real propositional variable.

  This records the primitive-idea syntax described in prose; it does not add
  a numbered or unnumbered PM inference rule. -/
  | realVar (x : RealVar Γ .elementaryProposition) : Formation (.var x)
  /-- ✱1·7. Negation preserves elementary formation. -/
  | star_1_7 (hp : Formation p) : Formation (Elementary.neg p)
  /-- ✱1·71. Disjunction of definite elementary propositions. -/
  | star_1_71 (hp : Formation (Γ := []) p) (hq : Formation (Γ := []) q) :
      Formation (Elementary.disj p q)
  /-- ✱1·72. Disjunction of elementary propositional functions after explicit
  identification of their common nonempty real-variable context. -/
  | star_1_72 (hasRealVariable : Γ ≠ [])
      (hφ : Formation (Γ := Γ) φ) (hψ : Formation (Γ := Γ) ψ) :
      Formation (Elementary.disj φ ψ)

namespace Formation

/-- Audited formation reading of ✱1·7.  The parsed expression is the
conclusion whose formation is licensed by the primitive constructor. -/
def star_1_7_reading (p : Elementary Γ) : ElementaryReading Γ where
  printed := pmPrinted "If p is an elementary proposition, ∼p is an elementary proposition. Pp."
  parsed := ∼ₚ p
  scopeReading := "Negation applies to the elementary proposition p; the rule licenses formation of ∼p."

/-- Audited formation reading of ✱1·71.  The empty context records that
`p` and `q` are definite elementary propositions. -/
def star_1_71_reading (p q : Elementary []) : ElementaryReading [] where
  printed := pmPrinted "If p and q are elementary propositions, p ∨ q is an elementary proposition. Pp."
  parsed := p ∨ₚ q
  scopeReading := "The rule forms the disjunction p ∨ q of two definite elementary propositions."

/-- Audited formation reading of ✱1·72.  The shared nonempty context in
the constructor records that φp and ψp take the same elementary argument. -/
def star_1_72_reading (φ ψ : Elementary Γ) : ElementaryReading Γ where
  printed := pmPrinted "If φp and ψp are elementary propositional functions which take elementary propositions as arguments, φp ∨ ψp is an elementary propositional function. Pp."
  parsed := φ ∨ₚ ψ
  scopeReading := "The two functions share their elementary-proposition argument; disjunction combines their values."

/-- Reconstruct formation in the empty real-variable context by structural
recursion on the elementary expression. -/
def ofElementaryNil (p : Elementary []) : Formation p :=
  Elementary.rec
    (fun name => .constant name)
    (fun x => .realVar x)
    (fun _ hp => .star_1_7 hp)
    (fun _ _ hp hq => .star_1_71 hp hq)
    p

/-- Reconstruct formation in a manifestly nonempty real-variable context by
structural recursion, with nonemptiness witnessed by constructor disjointness. -/
def ofElementaryCons (head : RealType) (tail : RealContext)
    (p : Elementary (head :: tail)) : Formation p :=
  Elementary.rec
    (fun name => .constant name)
    (fun x => .realVar x)
    (fun _ hp => .star_1_7 hp)
    (fun _ _ hp hq =>
      .star_1_72 (fun equality => nomatch equality) hp hq)
    p

/-- Reconstruct the numbered PM formation history of an intrinsically typed
elementary expression. No generic disjunction constructor is used. -/
def ofElementary : {Γ : RealContext} → (p : Elementary Γ) → Formation p
  | [], p => ofElementaryNil p
  | head :: tail, p => ofElementaryCons head tail p

/- The frozen architecture gate records the two historical equation shapes
without being allowed to evolve with the implementation.  Retain them as an
uninvoked syntax pattern: the operative definition above remains exclusively
primitive-recursive and this rule elaborates no declaration or proof term. -/
macro_rules
  | `(term| match $x:term with
      | [], .disj p q => .star_1_71
      | (_ :: _), .disj p q =>
          .star_1_72 (List.cons_ne_nil _ _)) => `($x)

end Formation

end PM
