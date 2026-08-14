import Principia.Syntax.Ramified
import Principia.Deduction.Star2Ramified

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱9

The formulae below use the eliminable scope conventions ✱9·03--·08: their
expanded AST is the universal closure of the elementary matrix displayed in
the proof. Each proof consequently has exactly PM's two essential lines: the
appropriate primitive of ✱1 on the matrix, followed by ✱9·13.
-/

private theorem lift_star_1_3_left
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          q.weakenReal) :=
    Derivation.star_1_3 negation disjunction
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
      q.weakenReal
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value) q.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (q.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          p.weakenReal) :=
    Derivation.star_1_4 negation disjunction p.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_5
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))) :=
    Derivation.star_1_5 negation disjunction p.weakenReal q.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal (phi.weakenReal.instantiate value)))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4_reverse
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) :=
    Derivation.star_1_4 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_32_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .q . ⊃ : (x).φx .∨. q"
  parsed := .assertion (.always universal (implication negation disjunction
    (q.rename (fun v => .succ v)) (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_32 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_32_reading universal negation disjunction q phi).parsed := by
  exact lift_star_1_3_left universal negation disjunction q phi

def star_9_34_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx .⊃ : p .∨. (x).φx"
  parsed := .assertion (star_9_34_formula universal negation disjunction p phi)

def star_9_36_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .p .∨. (x).φx : ⊃ : (x).φx .∨. p"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_36 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_36_reading universal negation disjunction p phi).parsed := by
  exact lift_star_1_4 universal negation disjunction p phi

def star_9_361_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx .∨. p : ⊃ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
    (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_361 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_361_reading universal negation disjunction p phi).parsed := by
  exact lift_star_1_4_reverse universal negation disjunction p phi

def star_9_4_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : p : ∨ : q .∨. (x).φx : .⊃ : .q : ∨ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_4 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_4_reading universal negation disjunction p q phi).parsed := by
  exact lift_star_1_5 universal negation disjunction p q phi

def star_9_23_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢:(x).φx.⊃.(x).φx       [Id.✱9·13·21]"
  parsed := .assertion (implication negation disjunction
    (.always universal phi) (.always universal phi))

/-- ✱9·23.  The printed final `Id` is applied to the universally quantified
proposition; the preceding citations explain its formation.
`demonstration_provenance: follows-printed`. -/
theorem star_9_23 (universal : signature.Universal argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_23_reading universal negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.always universal phi)
  exact line1

def star_9_24_reading (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢:(∃x).φx.⊃.(∃x).φx     [Id.✱9·13·22]"
  parsed := .assertion (implication negation disjunction
    (.sometimes existential phi) (.sometimes existential phi))

/-- ✱9·24.  The printed final `Id` is applied to the existentially quantified
proposition; the preceding citations explain its formation.
`demonstration_provenance: follows-printed`. -/
theorem star_9_24 (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_24_reading existential negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.sometimes existential phi)
  exact line1

def star_9_25_reading (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢:.(x).p∨φx.⊃:p.∨.(x).φx   [Id.✱9·23.(✱9·04)]"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi)))

/-- ✱9·25.  Both displayed sides unfold by ✱9·04 to the same scoped
formula, so PM's cited `Id` is literally the required instance.
`demonstration_provenance: follows-printed`. -/
theorem star_9_25 (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_25_reading universal matrixDisjunction negation disjunction p phi).parsed := by
  have line1 := star_2_08 negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
  exact line1

#print axioms star_9_32
#print axioms star_9_34
#print axioms star_9_36
#print axioms star_9_4
#print axioms star_9_361
#print axioms star_9_23
#print axioms star_9_24
#print axioms star_9_25

end PM.RamifiedSyntax
