import Principia.Syntax.Formula

namespace PM

/-- Explicit evidence that an elementary expression is licensed by PM's
primitive formation propositions.

Although `Elementary Γ` is intrinsically typed, this second judgement preserves
the historical distinction between formation in the empty context (✱1·71) and
identification of the real-variable type in a nonempty context (✱1·72). -/
inductive Formation : {Γ : RealContext} → Elementary Γ → Prop where
  /-- Admission of an elementary constant by the primitive idea, unnumbered. -/
  | constant (name : String) : Formation (.constant name)
  /-- Admission of a real propositional variable by the primitive idea,
  unnumbered. -/
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

/-- Reconstruct the numbered PM formation history of an intrinsically typed
elementary expression. No generic disjunction constructor is used. -/
def ofElementary : {Γ : RealContext} → (p : Elementary Γ) → Formation p
  | _, .constant name => .constant name
  | _, .var x => .realVar x
  | _, .neg p => .star_1_7 (ofElementary p)
  | [], .disj p q => .star_1_71 (ofElementary p) (ofElementary q)
  | (_ :: _), .disj p q =>
      .star_1_72 (List.cons_ne_nil _ _) (ofElementary p) (ofElementary q)

end Formation

end PM
