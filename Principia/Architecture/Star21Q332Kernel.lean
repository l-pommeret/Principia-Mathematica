/-!
# PM I, ✱21·11–✱21·13

Exact polymorphic binary-relation extensionality and function-formation
propositions.  Both relation arguments remain explicit and independently
typed.
-/

namespace PM.Architecture.Star21Q332Kernel

abbrev Relation (Left : Sort u) (Right : Sort v) := Left → Right → Prop

def ExtEq (psi chi : Relation Left Right) : Prop :=
  ∀ x y, psi x y ↔ chi x y

theorem relation_ext {psi chi : Relation Left Right} (h : ExtEq psi chi) :
    psi = chi := by
  funext x y
  exact propext (h x y)

/-- ✱21·11. A function of a relation respects formal equivalence of the
two-place matrices. -/
theorem star_21_11 (psi chi : Relation Left Right)
    (f : Relation Left Right → Prop) :
    ExtEq psi chi → (f psi ↔ f chi) := by
  intro h
  rw [relation_ext h]

/-- ✱21·111. Formal equivalence of `f` and `g` transfers from an arbitrary
predicative relation argument to its displayed relation abstraction. -/
theorem star_21_111 (phi : Relation Left Right)
    (f g : Relation Left Right → Prop) :
    (∀ relation, f relation ↔ g relation) → (f phi ↔ g phi) := by
  intro h
  exact h phi

/-- ✱21·112. Every proposition at the displayed relation argument has a
predicative function representative there. -/
theorem star_21_112 (phi : Relation Left Right)
    (f : Relation Left Right → Prop) :
    ∃ g : Relation Left Right → Prop, f phi ↔ g phi := by
  exact ⟨f, Iff.rfl⟩

/-- ✱21·12. A predicative representative of a binary relation can be
chosen so that `f` has the same value on both extensions. -/
theorem star_21_12 (psi : Relation Left Right)
    (f : Relation Left Right → Prop) :
    ∃ phi : Relation Left Right, ExtEq phi psi ∧ (f psi ↔ f phi) := by
  exact ⟨psi, fun _ _ => Iff.rfl, Iff.rfl⟩

/-- ✱21·13. Formally equivalent binary matrices determine the same
relation extension. -/
theorem star_21_13 (psi chi : Relation Left Right) :
    ExtEq psi chi → psi = chi :=
  relation_ext

end PM.Architecture.Star21Q332Kernel
