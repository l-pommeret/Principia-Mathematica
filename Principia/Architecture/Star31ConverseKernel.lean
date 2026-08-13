namespace PM.Architecture.Star31ConverseKernel

/-! Nine consecutive exact converse-of-relations propositions, PM I
✱31·11–✱31·16. Relations are homogeneous typed binary predicates. -/

abbrev Relation (α : Type u) := α → α → Prop

def converse (P : Relation α) : Relation α := fun x y => P y x
def IsConverse (Q P : Relation α) : Prop := ∀ x y, Q x y ↔ P y x
def Cnv (P : Relation α) : Relation α := converse P
def inter (P Q : Relation α) : Relation α := fun x y => P x y ∧ Q x y
def union (P Q : Relation α) : Relation α := fun x y => P x y ∨ Q x y
def compl (P : Relation α) : Relation α := fun x y => ¬ P x y

/-- ✱31·11. `x P̌ y ↔ y P x`. -/
theorem star_31_11 (P : Relation α) (x y : α) :
    converse P x y ↔ P y x := Iff.rfl

/-- ✱31·111. The converse extension bears `Cnv` to its source. -/
theorem star_31_111 (P : Relation α) : IsConverse (converse P) P :=
  fun _ _ => Iff.rfl

/-- ✱31·12. The explicit converse equals `CnvʻP`. -/
theorem star_31_12 (P : Relation α) : converse P = Cnv P := rfl

/-- ✱31·13. `CnvʻP` exists. -/
theorem star_31_13 (P : Relation α) : ∃ Q, IsConverse Q P :=
  ⟨Cnv P, fun _ _ => Iff.rfl⟩

/-- ✱31·131. `x(CnvʻP)y ↔ yPx`. -/
theorem star_31_131 (P : Relation α) (x y : α) :
    Cnv P x y ↔ P y x := Iff.rfl

/-- ✱31·132. A relation is converse to `P` iff it equals `CnvʻP`, iff it
equals the explicit converse. -/
theorem star_31_132 (Q P : Relation α) :
    (IsConverse Q P ↔ Q = Cnv P) ∧ (Q = Cnv P ↔ Q = converse P) := by
  constructor
  · constructor
    · intro h
      funext x y
      exact propext (h x y)
    · rintro rfl
      exact fun _ _ => Iff.rfl
  · exact Iff.rfl

/-- ✱31·14. Converse distributes over relation intersection. -/
theorem star_31_14 (P Q : Relation α) :
    Cnv (inter P Q) = inter (Cnv P) (Cnv Q) := rfl

/-- ✱31·15. Converse distributes over relation union. -/
theorem star_31_15 (P Q : Relation α) :
    Cnv (union P Q) = union (Cnv P) (Cnv Q) := rfl

/-- ✱31·16. Converse commutes with relation complementation. -/
theorem star_31_16 (P : Relation α) :
    Cnv (compl P) = compl (Cnv P) := rfl

end PM.Architecture.Star31ConverseKernel
