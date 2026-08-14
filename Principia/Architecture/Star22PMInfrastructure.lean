import Principia.Syntax.Class

/-!
# PM I ✱22 — class-calculus infrastructure

The five opening `Df` lines are eliminable definitions supplied by
`Principia.Syntax.Class`; none is a constructor of a derivability relation.
-/

namespace PM.Architecture.Star22PMInfrastructure

open PM.ClassSyntax

/-- ✱22·01 unfolds inclusion to universal pointwise implication. -/
theorem star_22_01_unfold (alpha beta : ClassTerm Object) :
    included alpha beta =
      .forallObject (fun x => .implies (.membership x alpha) (.membership x beta)) := rfl

/-- ✱22·02 unfolds intersection to abstraction of conjunction. -/
theorem star_22_02_unfold (alpha beta : ClassTerm Object) :
    intersection alpha beta =
      .abstraction (fun x => alpha.membership x ∧ beta.membership x) := rfl

/-- ✱22·03 unfolds union to abstraction of disjunction. -/
theorem star_22_03_unfold (alpha beta : ClassTerm Object) :
    union alpha beta =
      .abstraction (fun x => alpha.membership x ∨ beta.membership x) := rfl

/-- ✱22·04 unfolds complement to abstraction of non-membership. -/
theorem star_22_04_unfold (alpha : ClassTerm Object) :
    complement alpha = .abstraction (fun x => ¬ alpha.membership x) := rfl

/-- ✱22·05 unfolds difference to intersection with complement. -/
theorem star_22_05_unfold (alpha beta : ClassTerm Object) :
    difference alpha beta = intersection alpha (complement beta) := rfl

end PM.Architecture.Star22PMInfrastructure
