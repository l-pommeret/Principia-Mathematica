import Principia.Architecture.FirstOrderPrerequisites

namespace PM.Architecture.JudgementNaturality

open PM.Architecture.FirstOrderPrerequisites

/-! Substitution of the leading real propositional variable.  This is PM's
schematic substitution discipline, not an object-language inference rule. -/

def substituteElementaryHead (replacement : Elementary Γ) :
    Elementary (.elementaryProposition :: Γ) → Elementary Γ
  | .constant name => .constant name
  | .var .zero => replacement
  | .var (.succ v) => .var v
  | .neg proposition => .neg (substituteElementaryHead replacement proposition)
  | .disj left right => .disj
      (substituteElementaryHead replacement left)
      (substituteElementaryHead replacement right)

def headSchemaAssignment (replacement : Elementary Γ) :
    Elementary.SchemaAssignment (.elementaryProposition :: Γ) Γ
  | .zero => replacement
  | .succ v => .var v

@[simp] theorem schemaInstance_headAssignment (replacement : Elementary Γ)
    (p : Elementary (.elementaryProposition :: Γ)) :
    Elementary.schemaInstance (headSchemaAssignment replacement) p =
      substituteElementaryHead replacement p := by
  induction p with
  | constant name => rfl
  | var v => cases v <;> rfl
  | neg p ih => simp [Elementary.schemaInstance, substituteElementaryHead, ih]
  | disj p q ihp ihq => simp [Elementary.schemaInstance, substituteElementaryHead, ihp, ihq]

theorem derivation_substituteHead (replacement : Elementary Γ) {p}
    (proof : Derivation (Γ := .elementaryProposition :: Γ) p) :
    Derivation (substituteElementaryHead replacement p) := by
  rw [← schemaInstance_headAssignment]
  exact Derivation.instantiateSchema (headSchemaAssignment replacement) proof

def substituteApparentHead (replacement : Elementary Γ) :
    Apparent (.elementaryProposition :: Γ) Δ → Apparent Γ Δ
  | .constant name => .constant name
  | .real .zero => Apparent.ofElementary replacement
  | .real (.succ v) => .real v
  | .bound v => .bound v
  | .neg proposition => .neg (substituteApparentHead replacement proposition)
  | .disj left right => .disj
      (substituteApparentHead replacement left)
      (substituteApparentHead replacement right)

def substituteFirstOrderHead (replacement : Elementary Γ) :
    FirstOrder (.elementaryProposition :: Γ) Δ → FirstOrder Γ Δ
  | .always body => .always (substituteApparentHead replacement body)
  | .sometimes body => .sometimes (substituteApparentHead replacement body)

@[simp] theorem substituteApparentHead_weaken
    (replacement : Elementary Γ) (body : Apparent Γ Δ) :
    substituteApparentHead replacement (Apparent.weakenReal body) = body := by
  induction body with
  | constant name => simp [Apparent.weakenReal, Apparent.renameReal, substituteApparentHead]
  | real v => simp [Apparent.weakenReal, Apparent.renameReal, substituteApparentHead]
  | bound v => simp [Apparent.weakenReal, Apparent.renameReal, substituteApparentHead]
  | neg proposition ih =>
      change Apparent.neg
        (substituteApparentHead replacement (Apparent.weakenReal proposition)) =
          Apparent.neg proposition
      rw [ih]
  | disj left right ihl ihr =>
      change Apparent.disj
        (substituteApparentHead replacement (Apparent.weakenReal left))
        (substituteApparentHead replacement (Apparent.weakenReal right)) =
          Apparent.disj left right
      rw [ihl, ihr]

@[simp] theorem substituteFirstOrderHead_weaken
    (replacement : Elementary Γ) (proposition : FirstOrder Γ Δ) :
    substituteFirstOrderHead replacement (FirstOrder.weakenReal proposition) = proposition := by
  cases proposition <;> simp [FirstOrder.weakenReal, substituteFirstOrderHead]

end PM.Architecture.JudgementNaturality
