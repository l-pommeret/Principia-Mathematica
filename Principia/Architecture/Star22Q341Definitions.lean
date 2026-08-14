/-!
# PM I, ✱22·01–✱22·05

Exact extensional definitions opening the calculus of classes.
-/

namespace PM.Architecture.Star22Q341Definitions

abbrev Class (Object : Sort u) := Object → Prop

/-- ✱22·01: class inclusion is formal implication at every member. -/
def Included (alpha beta : Class Object) : Prop :=
  ∀ x, alpha x → beta x

/-- ✱22·01. α ⊂ β .=: x ε α .⊃ₓ. x ε β Df -/
def star_22_01 (alpha beta : Class Object) : Prop :=
  ∀ x, alpha x → beta x

/-- ✱22·02: intersection is the class abstraction of conjunction. -/
def Intersection (alpha beta : Class Object) : Class Object :=
  fun x => alpha x ∧ beta x

/-- ✱22·02. α ∩ β = ẑx(x ε α . x ε β) Df -/
def star_22_02 (alpha beta : Class Object) : Class Object :=
  Intersection alpha beta

/-- ✱22·03: union is the class abstraction of disjunction. -/
def Union (alpha beta : Class Object) : Class Object :=
  fun x => alpha x ∨ beta x

/-- ✱22·03. α ∪ β = ẑx(x ε α .∨. x ε β) Df -/
def star_22_03 (alpha beta : Class Object) : Class Object :=
  Union alpha beta

/-- ✱22·04: complement is the class abstraction of non-membership. -/
def Complement (alpha : Class Object) : Class Object :=
  fun x => ¬ alpha x

/-- ✱22·04. −α = ẑx(x ∼ε α) Df -/
def star_22_04 (alpha : Class Object) : Class Object :=
  fun x => ¬ alpha x

/-- ✱22·05: class difference is intersection with the complement. -/
def Difference (alpha beta : Class Object) : Class Object :=
  Intersection alpha (Complement beta)

/-- ✱22·05. α − β = α ∩ −β Df -/
def star_22_05 (alpha beta : Class Object) : Class Object :=
  Intersection alpha (Complement beta)

end PM.Architecture.Star22Q341Definitions
