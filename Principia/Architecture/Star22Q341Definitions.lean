/-!
# PM I, ✱22·01–✱22·05

Exact extensional definitions opening the calculus of classes.
-/

namespace PM.Architecture.Star22Q341Definitions

abbrev Class (Object : Sort u) := Object → Prop

/-- ✱22·01: class inclusion is formal implication at every member. -/
def Included (alpha beta : Class Object) : Prop :=
  ∀ x, alpha x → beta x

theorem star_22_01 (alpha beta : Class Object) :
    Included alpha beta = (∀ x, alpha x → beta x) := rfl

/-- ✱22·02: intersection is the class abstraction of conjunction. -/
def Intersection (alpha beta : Class Object) : Class Object :=
  fun x => alpha x ∧ beta x

theorem star_22_02 (alpha beta : Class Object) :
    Intersection alpha beta = fun x => alpha x ∧ beta x := rfl

/-- ✱22·03: union is the class abstraction of disjunction. -/
def Union (alpha beta : Class Object) : Class Object :=
  fun x => alpha x ∨ beta x

theorem star_22_03 (alpha beta : Class Object) :
    Union alpha beta = fun x => alpha x ∨ beta x := rfl

/-- ✱22·04: complement is the class abstraction of non-membership. -/
def Complement (alpha : Class Object) : Class Object :=
  fun x => ¬ alpha x

theorem star_22_04 (alpha : Class Object) :
    Complement alpha = fun x => ¬ alpha x := rfl

/-- ✱22·05: class difference is intersection with the complement. -/
def Difference (alpha beta : Class Object) : Class Object :=
  Intersection alpha (Complement beta)

theorem star_22_05 (alpha beta : Class Object) :
    Difference alpha beta = Intersection alpha (Complement beta) := rfl

end PM.Architecture.Star22Q341Definitions
