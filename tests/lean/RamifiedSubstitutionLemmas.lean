import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax.SubstitutionRegression

universe u

variable {signature : Signature.{u}}
variable {real source target : Context}
variable {order : Nat} {sort fresh argument : RSort}

theorem substitute_identity
    (formula : Formula signature real source order)
    (sigma : Substitution signature real source source)
    (identity : IsIdentitySubstitution sigma) :
    formula.substitute sigma = formula :=
  Formula.substitute_eq_self formula identity

theorem weakening_commutes_with_renaming
    (formula : Formula signature real source order)
    (rho : Renaming source target) :
    (formula.rename rho).weakenReal (fresh := fresh) =
      formula.weakenReal.rename rho :=
  Formula.weakenReal_rename formula rho

theorem closed_formula_survives_instantiation
    (formula : Formula signature real [] order)
    (value : Term signature (argument :: real) [] argument) :
    ((formula.rename (fun v => .succ v) :
        Formula signature real [argument] order).weakenReal
          (fresh := argument)).instantiate value =
      formula.weakenReal :=
  Formula.closed_weakenReal_instantiate formula argument value

end PM.RamifiedSyntax.SubstitutionRegression
