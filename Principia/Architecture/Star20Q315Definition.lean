namespace PM.Architecture.Star20Q315Definition

/-- A class at the element type `α`, represented extensionally but kept at
its own type level. -/
abbrev Class (α : Sort u) := α → Prop

/-- The extension `ẑ(φ!z)` of a predicative-function code.  The code type
`κ` is deliberately abstract: ✱20·03 does not identify arbitrary functions
with predicative functions. -/
def extension (representation : κ → Class α) (φ : κ) : Class α :=
  representation φ

/-- The type-relative class `Cls`: precisely those classes which are the
extension of a predicative-function code.  Its carrier is one level above
the element class, so this does not form an untyped universal class. -/
def Cls (representation : κ → Class α) : Class (Class α) :=
  fun candidate => ∃ φ, candidate = extension representation φ

/-- Exact reductional reading of PM I ✱20·03:
`Cls = ẑ((∃φ). α = ẑ(φ!z))`. -/
def star_20_03 (representation : κ → Class α) : Class (Class α) :=
  fun candidate => ∃ φ, candidate = extension representation φ

end PM.Architecture.Star20Q315Definition
