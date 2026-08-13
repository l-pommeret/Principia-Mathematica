namespace PM.Architecture.Star81ClosingKernel
universe u v
abbrev Set (X : Type u) := X → Prop
abbrev Rel (X : Type u) (Y : Type v) := X → Y → Prop
def Fibre (P : Rel X Y) (y : Y) : Set X := fun x => P x y
def FibreFamily (P : Rel X Y) (K : Set Y) : Set (Set X) := fun A => ∃y, K y ∧ A = Fibre P y
def Included (A B : Set X) := ∀x, A x → B x
def UnionFamily (L : Set (Set X)) : Set X := fun x => ∃A, L A ∧ A x
def OneIntersection (M A : Set X) := ∃x, M x ∧ A x ∧ ∀z, M z → A z → z=x
def RepresentativeDomains (L : Set (Set X)) : Set (Set X) := fun M =>
  (∀A, L A → OneIntersection M A) ∧ Included M (UnionFamily L)

/-- PM I ✱81·3: the possible domains depend exactly on the family of fibres. -/
theorem star_81_3 (P : Rel X Y) (K : Set Y) :
    RepresentativeDomains (FibreFamily P K) =
      fun M => (∀A, FibreFamily P K A → OneIntersection M A) ∧
        Included M (UnionFamily (FibreFamily P K)) := rfl

/-- PM I ✱81·31. -/
theorem star_81_31 (P Q : Rel X Y) (K : Set Y)
    (h : FibreFamily P K = FibreFamily Q K) :
    RepresentativeDomains (FibreFamily P K) = RepresentativeDomains (FibreFamily Q K) := by
  rw [h]

end PM.Architecture.Star81ClosingKernel
