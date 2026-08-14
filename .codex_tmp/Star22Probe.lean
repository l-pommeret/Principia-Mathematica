import Principia.Deduction.Star10Derived

namespace PM.RamifiedSyntax

private theorem bindOrder_succ_individual_probe (order : Nat) :
    bindOrder (Nat.succ order) .individual = Nat.succ order := by
  cases order with
  | zero => rfl
  | succ order => rfl

private def ramifiedConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

def star_10_3_probe_reading
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (phi psi chi : Formula signature real [.individual] (Nat.succ order)) :
    ClaimReading signature real where
  printed := "✱10·3.  ⊢ : .(x).φx⊃ψx : (x).ψx⊃χx : ⊃ .(x).φx⊃χx"
  parsed := .assertion (.always universal
    (implication negation disjunction
      (ramifiedConjunction negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction psi chi))
      (implication negation disjunction phi chi)))

theorem star_10_3_probe
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (phi psi chi : Formula signature real [.individual] (Nat.succ order)) :
    Derivation (star_10_3_probe_reading universal negation disjunction
      phi psi chi).parsed := by
  let body := implication negation disjunction
    (ramifiedConjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi chi))
    (implication negation disjunction phi chi)
  let value : Term signature (.individual :: real) [] .individual :=
    .real (.zero : Var (.individual :: real) .individual)
  have line1 : Derivation (.assertion (body.weakenReal.instantiate value)) := by
    unfold body
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    unfold ramifiedConjunction
    exact star_3_33 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

#print axioms star_10_3_probe

end PM.RamifiedSyntax
