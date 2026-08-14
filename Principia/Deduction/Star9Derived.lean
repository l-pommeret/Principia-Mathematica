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
    Derivation.star_1_3_same negation disjunction
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

private theorem lift_star_1_2
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) :=
    Derivation.star_1_2 negation disjunction
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi phi) phi)
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
    Derivation.star_1_4_same negation disjunction p.weakenReal
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
    Derivation.star_1_5_same negation disjunction p.weakenReal q.weakenReal
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
    Derivation.star_1_4_same negation disjunction
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

def star_9_2_reading
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    ClaimReading signature real where
  printed := "⊢:(x).φx.⊃.φy"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal phi) (phi.instantiate y))

/-- ✱9·2 is the general-to-particular inference later restated as ✱10·1.
The canonical block prints no demonstration, so the later primitive restatement
is used as the reconstruction.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_2
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    Derivation (star_9_2_reading universal negation disjunction phi y).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction phi y
  exact line1

def star_9_3_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx .∨. (x).φx : ⊃ . (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi phi) phi))

/-- The eliminable scope definitions reduce the printed proof to its
elementary `Taut` matrix and the final generalization.
`demonstration_provenance: follows-printed`. -/
theorem star_9_3 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_3_reading universal negation disjunction phi).parsed := by
  exact lift_star_1_2 universal negation disjunction phi

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

def star_9_41_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : p : ∨ : (x).φx .∨. r : .⊃ : .(x).φx : ∨ : p ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_41 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_41_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction p.weakenReal
      (phi.weakenReal.instantiate value) r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))))
  exact line2

def star_9_42_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : (x).φx : ∨ : q ∨ r : .⊃ : .q : ∨ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_42 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_42_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction
      (phi.weakenReal.instantiate value) q.weakenReal r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
  exact line2

def star_9_51_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : p .⊃. (x).φx : ⊃ : .p ∨ r .⊃ .⊃ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v)) phi)
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_51 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_51_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal p.weakenReal
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v)) phi)
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution]
    rfl
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v)) phi)
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_21_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢:.(x).φx⊃ψx.⊃:.(x).φx.⊃.(x).ψx"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction phi psi)
    (implication negation disjunction phi psi)))

/-- The scope definitions collapse PM's intermediate existential forms to the
closed identity matrix before the final use of ✱9·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_21 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Derivation (star_9_21_reading universal negation disjunction phi psi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)) :=
    star_2_08 negation disjunction
      (implication negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction phi psi)).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute, implication_weakenReal,
      implication_substitute, Formula.instantiate, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction phi psi))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_31_reading
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(∃x).φx .∨. (∃x).φx : ⊃ . (∃x).φx"
  parsed := .assertion (implication negation disjunction
    (sameDisjunction disjunction (.sometimes existential phi)
      (.sometimes existential phi))
    (.sometimes existential phi))

/-- The exact first-order `Taut` instance is available without a premise.
This reconstruction does not claim PM's longer ✱9·11 route.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_31
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_31_reading existential negation disjunction phi).parsed := by
  have line1 := Derivation.star_1_2 negation disjunction
    (.sometimes existential phi)
  exact line1

def star_9_33_reading
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (innerDisjunction : signature.Disjunction
      (max (bindOrder 0 argument) 0))
    (outerDisjunction : signature.Disjunction
      (max 0 (max (bindOrder 0 argument) 0)))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .q .⊃ : (∃x).φx .∨. q   [Proof as above]"
  parsed := .assertion (mixedImplication negation outerDisjunction q
    (.disj innerDisjunction (.sometimes existential phi) q))

/-- The existential target is the corresponding assigned-order `Add`
instance.  Its proof is unconditional but uses typical ambiguity directly.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_33
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (innerDisjunction : signature.Disjunction
      (max (bindOrder 0 argument) 0))
    (outerDisjunction : signature.Disjunction
      (max 0 (max (bindOrder 0 argument) 0)))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_33_reading existential negation innerDisjunction
      outerDisjunction q phi).parsed := by
  have line1 := Derivation.star_1_3 negation innerDisjunction
    outerDisjunction (.sometimes existential phi) q
  exact line1

def star_9_35_reading
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (innerDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder 0 argument) (max 0 (bindOrder 0 argument))))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(∃x).φx .⊃ : p .∨. (∃x).φx   [Proof as above]"
  parsed := .assertion (mixedImplication negation outerDisjunction
    (.sometimes existential phi)
    (.disj innerDisjunction p (.sometimes existential phi)))

/-- The existential target is the corresponding assigned-order `Add`
instance.  Its proof is unconditional but uses typical ambiguity directly.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_35
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (innerDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder 0 argument) (max 0 (bindOrder 0 argument))))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_35_reading existential negation innerDisjunction
      outerDisjunction p phi).parsed := by
  have line1 := Derivation.star_1_3 negation innerDisjunction
    outerDisjunction p (.sometimes existential phi)
  exact line1

def star_9_5_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : p ⊃ q .⊃ : .p .∨. (x).φx : ⊃ : q .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v))
      (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))))

/-- PM's first line is reconstructed by the derived right-summation form of
`Sum`, then lifted through ✱9·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_5 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_5_reading universal negation disjunction p q phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) :=
    star_2_38 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v))
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
          (sameDisjunction disjunction
            (q.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v))
        (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_52_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : : (x).φx .⊃. q : ⊃ : .(x).φx .∨. r .⊃ . q ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction phi (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

/-- PM's first line is reconstructed by the derived right-summation form of
`Sum`, then lifted through ✱9·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_52 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_52_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal
      (phi.weakenReal.instantiate value) q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction phi
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction phi (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_61_reading
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "If φx̂ and ψx̂ are elementary functions of the same type, there is a function φx̂ ∨ ψx̂."
  parsed := .functionExistence (sameDisjunction disjunction phi psi)

/-- ✱9·61. Intrinsic typing supplies PM's same-type hypothesis, and the
printed appeal to ✱9·15 is the primitive function-existence constructor.
`demonstration_provenance: follows-printed`. -/
theorem star_9_61
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_61_reading disjunction phi psi).parsed := by
  have line1 := Derivation.star_10_121 psi
  have line2 := Derivation.star_10_121 phi
  have line3 := Derivation.star_10_121
    (sameDisjunction disjunction phi psi)
  have line4 := Derivation.star_10_122
    (sameDisjunction disjunction phi psi)
  exact line4

/-- The two function matrices printed at ✱9·62.  The index lets one theorem
assert both heterogeneous `Claim.functionExistence` conclusions without
adding a conjunction or a new constructor to the object calculus. -/
inductive Star9_62Branch where
  | universal
  | existential

def star_9_62_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_62Branch.casesOn branch
    (.always universal (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))
    (.sometimes existential (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))

def star_9_62_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    ClaimReading signature real where
  printed := "If φ(x̂, ŷ) and ψẑ are elementary functions, and the x-argument to φ is of the same type as the argument to ψ, there are functions (y).φ(x̂,y).∨.ψx̂, (∃y).φ(x̂,y).∨.ψx̂."
  parsed := .functionExistence
    (star_9_62_matrix universal existential disjunction phi psi branch)

/-- ✱9·62, for each of the two function matrices named in print.  Intrinsic
sorting supplies the same-type premise; ✱10·121/·122 are the ramified forms
of the cited ✱9·14/·15 formation steps.
`demonstration_provenance: follows-printed`. -/
theorem star_9_62
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Derivation (star_9_62_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_62_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_62_matrix universal existential disjunction phi psi branch)
  exact line2

/-- The four always/sometimes combinations covered by PM's “etc.” at ✱9·63. -/
inductive Star9_63Branch where
  | universalUniversal
  | universalExistential
  | existentialUniversal
  | existentialExistential

def star_9_63_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_63Branch.casesOn branch
    (sameDisjunction disjunction (.always universal phi) (.always universal psi))
    (sameDisjunction disjunction (.always universal phi) (.sometimes existential psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.always universal psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.sometimes existential psi))

def star_9_63_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    ClaimReading signature real where
  printed := "If φ(x̂, ŷ), ψ(x̂, ŷ) are elementary functions of the same type, there are functions (y).φ(x̂,y).∨.(z).ψ(x̂,z), etc.  [Proof as above]"
  parsed := .functionExistence
    (star_9_63_matrix universal existential disjunction phi psi branch)

/-- ✱9·63, uniformly for all four branches meant by “etc.”.  The formation
claim stays inside `Derivation` and introduces no extra primitive.
`demonstration_provenance: follows-printed`. -/
theorem star_9_63
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Derivation (star_9_63_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_63_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_63_matrix universal existential disjunction phi psi branch)
  exact line2

#print axioms star_9_32
#print axioms star_9_2
#print axioms star_9_3
#print axioms star_9_34
#print axioms star_9_36
#print axioms star_9_4
#print axioms star_9_361
#print axioms star_9_23
#print axioms star_9_24
#print axioms star_9_25
#print axioms star_9_41
#print axioms star_9_42
#print axioms star_9_51
#print axioms star_9_21
#print axioms star_9_31
#print axioms star_9_33
#print axioms star_9_35
#print axioms star_9_5
#print axioms star_9_52
#print axioms star_9_61
#print axioms star_9_62
#print axioms star_9_63

end PM.RamifiedSyntax
