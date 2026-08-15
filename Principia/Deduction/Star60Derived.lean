import Principia.FirstEdition.Volume1.Star60Source
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived definitions of PM I, ✱60

`Cl ex` is an incomplete relation sign.  Its application to `κ, α` expands
the inner class abstraction `β̂(β ⊂ α . ∃!β)` inside the continuation which
reads `κ = β̂(...)`.  The argument sort is left explicit because the `β` of
✱60·02 is itself a class at the relevant systematic-ambiguity instance.
-/

/-- ✱60·02, the eliminable contextual expansion of
`Cl ex = κ̂α̂{κ = β̂(β ⊂ α . ∃!β)}`.  `inclusion` and `existence` are the two
printed members of the matrix, while `continuation` is its displayed
identity with `κ`. -/
def star_60_02
    (existential : ExistentialVocabulary signature
      (.function [betaSort] (max inclusionOrder existenceOrder) 0)
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (universal : signature.Universal betaSort
      (max inclusionOrder existenceOrder))
    (equivalenceNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (equivalenceDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (inclusionNegation : signature.Negation inclusionOrder)
    (existenceNegation : signature.Negation existenceOrder)
    (conditionNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (conditionDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (leftNegation : signature.Negation
      (bindOrder (max inclusionOrder existenceOrder) betaSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (inclusion : Formula signature real (betaSort :: apparent)
      inclusionOrder)
    (existence : Formula signature real (betaSort :: apparent)
      existenceOrder)
    (continuation : Formula signature real
      (.function [betaSort] (max inclusionOrder existenceOrder) 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
          scopeOrder)
        (.function [betaSort] (max inclusionOrder existenceOrder) 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          ((mixedConjunction inclusionNegation existenceNegation
            conditionNegation conditionDisjunction inclusion existence).rename
              (liftRenaming (fun v => .succ v)))))
      continuation)

/-- The complete eliminable expansion printed at ✱60·02. -/
theorem star_60_02_unfold
    (existential : ExistentialVocabulary signature
      (.function [betaSort] (max inclusionOrder existenceOrder) 0)
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (universal : signature.Universal betaSort
      (max inclusionOrder existenceOrder))
    (equivalenceNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (equivalenceDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (inclusionNegation : signature.Negation inclusionOrder)
    (existenceNegation : signature.Negation existenceOrder)
    (conditionNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (conditionDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (leftNegation : signature.Negation
      (bindOrder (max inclusionOrder existenceOrder) betaSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (inclusion : Formula signature real (betaSort :: apparent)
      inclusionOrder)
    (existence : Formula signature real (betaSort :: apparent)
      existenceOrder)
    (continuation : Formula signature real
      (.function [betaSort] (max inclusionOrder existenceOrder) 0 :: apparent)
      scopeOrder) :
    star_60_02 existential universal equivalenceNegation
        equivalenceDisjunction inclusionNegation existenceNegation
        conditionNegation conditionDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction inclusion existence continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              ((mixedConjunction inclusionNegation existenceNegation
                conditionNegation conditionDisjunction inclusion
                existence).rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-- Diplomatic reading of the definition ✱60·02. -/
def star_60_02_reading
    (existential : ExistentialVocabulary signature
      (.function [betaSort] (max inclusionOrder existenceOrder) 0)
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (universal : signature.Universal betaSort
      (max inclusionOrder existenceOrder))
    (equivalenceNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (equivalenceDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (inclusionNegation : signature.Negation inclusionOrder)
    (existenceNegation : signature.Negation existenceOrder)
    (conditionNegation : signature.Negation
      (max inclusionOrder existenceOrder))
    (conditionDisjunction : signature.Disjunction
      (max inclusionOrder existenceOrder))
    (leftNegation : signature.Negation
      (bindOrder (max inclusionOrder existenceOrder) betaSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (max inclusionOrder existenceOrder) betaSort)
        scopeOrder))
    (inclusion : Formula signature real [betaSort] inclusionOrder)
    (existence : Formula signature real [betaSort] existenceOrder)
    (continuation : Formula signature real
      [.function [betaSort] (max inclusionOrder existenceOrder) 0]
      scopeOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱60·02. Cl ex = κ̂α̂{κ = β̂(β ⊂ α . ∃!β)} Df"
  parsed := .assertion
    (star_60_02 existential universal equivalenceNegation
      equivalenceDisjunction inclusionNegation existenceNegation
      conditionNegation conditionDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction inclusion existence continuation)
  scopeReading := "The inner beta abstraction has the scope of the displayed identity with kappa; inclusion and class existence are its two conjuncts."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_60_02
#print axioms PM.RamifiedSyntax.star_60_02_unfold
#print axioms PM.RamifiedSyntax.star_60_02_reading
