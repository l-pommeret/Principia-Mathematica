namespace PM.ClassSyntax

/-- Class terms introduced by the five definitions at PM I ✱22·01–05. -/
inductive ClassTerm (Object : Type u) where
  | variable (name : String) (membership : Object → Prop)
  | abstraction (matrix : Object → Prop)
  | intersection (left right : ClassTerm Object)
  | union (left right : ClassTerm Object)
  | complement (term : ClassTerm Object)

/-- Secondary extensional interpretation, never itself a derivability
judgement. -/
def ClassTerm.membership : ClassTerm Object → Object → Prop
  | .variable _ predicate => predicate
  | .abstraction matrix => matrix
  | .intersection left right => fun x => left.membership x ∧ right.membership x
  | .union left right => fun x => left.membership x ∨ right.membership x
  | .complement term => fun x => ¬ term.membership x

/-- Object-language class formulae. -/
inductive Formula (Object : Type u) where
  | membership (object : Object) (classTerm : ClassTerm Object)
  | implies (left right : Formula Object)
  | conjunction (left right : Formula Object)
  | disjunction (left right : Formula Object)
  | negation (formula : Formula Object)
  | forallObject (body : Object → Formula Object)
  | classhood (term : ClassTerm Object)
  | classEquality (left right : ClassTerm Object)
  | equivalent (left right : Formula Object)

/-- Assertion endpoint for the class fragment. A derivability relation will be
added only when its genuinely primitive/rule constructors are source-audited. -/
inductive Judgement (Object : Type u) where
  | asserted (formula : Formula Object)

/-! The five printed `Df` lines are abbreviations, never derivation rules. -/

def included (alpha beta : ClassTerm Object) : Formula Object :=
  .forallObject (fun x => .implies (.membership x alpha) (.membership x beta))

def intersection (alpha beta : ClassTerm Object) : ClassTerm Object :=
  .abstraction (fun x => alpha.membership x ∧ beta.membership x)

def union (alpha beta : ClassTerm Object) : ClassTerm Object :=
  .abstraction (fun x => alpha.membership x ∨ beta.membership x)

def complement (alpha : ClassTerm Object) : ClassTerm Object :=
  .abstraction (fun x => ¬ alpha.membership x)

def difference (alpha beta : ClassTerm Object) : ClassTerm Object :=
  intersection alpha (complement beta)

/-! Parsed endpoints prepared for ✱22·37–392.  They are syntax only; no
derivability constructor is introduced for these derived propositions. -/

def star_22_37_formula (alpha beta : ClassTerm Object) : Formula Object :=
  .classhood (union alpha beta)

def star_22_38_formula (alpha : ClassTerm Object) : Formula Object :=
  .classhood (complement alpha)

def star_22_39_formula (phi psi : Object → Prop) : Formula Object :=
  .classEquality
    (.intersection (.abstraction phi) (.abstraction psi))
    (.abstraction (fun z => phi z ∧ psi z))

def star_22_391_formula (phi psi : Object → Prop) : Formula Object :=
  .classEquality
    (.union (.abstraction phi) (.abstraction psi))
    (.abstraction (fun z => phi z ∨ psi z))

def star_22_392_formula (phi : Object → Prop) : Formula Object :=
  .classEquality (.complement (.abstraction phi))
    (.abstraction (fun z => ¬ phi z))

end PM.ClassSyntax
