/-! PM I, ✱55·01–✱55·201: ordinal couples, typed extensional semantics. -/
namespace PM.Architecture.Star55OpeningKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def singleton (x : α) : Class α := fun z => z = x
def cross (A B : Class α) : Rel α := fun x y => A x ∧ B y
def pair (x y : α) : Rel α := cross (singleton x) (singleton y)
def converse (R : Rel α) : Rel α := fun x y => R y x
def domain (R : Rel α) : Class α := fun x => ∃ y, R x y
def codomain (R : Rel α) : Class α := fun y => ∃ x, R x y
def field (R : Rel α) : Class α := fun x => domain R x ∨ codomain R x
def pairValue (F : Rel α → β) (x y : α) : β := F (pair x y)

private theorem rel_ext {R S : Rel α} (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y; exact propext (h x y)
private theorem class_ext {A B : Class α} (h : ∀ x, A x ↔ B x) : A = B := by
  funext x; exact propext (h x)

/-- ✱55·01. Definition of the ordinal couple. -/
def star_55_01 (x y : α) : Rel α := cross (singleton x) (singleton y)
/-- ✱55·02. Substitution of an ordinal couple as argument. -/
def star_55_02 (F : Rel α → β) (x y : α) : β := F (pair x y)
/-- ✱55·1. The defining equation. -/
theorem star_55_1 (x y : α) : pair x y = cross (singleton x) (singleton y) := rfl
/-- ✱55·11. The three notations denote the same unique couple. -/
theorem star_55_11 (x y : α) : (fun z => pair x z) y = pair x y ∧ pair x y = cross (singleton x) (singleton y) := ⟨rfl,rfl⟩
/-- ✱55·12. The value of the left pair-constructor exists uniquely. -/
theorem star_55_12 (x y : α) : ∃ R : Rel α, R = pair x y ∧ ∀ S, S = pair x y → S = R :=
  ⟨pair x y,rfl,fun _ h=>h⟩
/-- ✱55·121. The value of the right pair-constructor exists uniquely. -/
theorem star_55_121 (x y : α) : ∃ R : Rel α, R = pair x y ∧ ∀ S, S = pair x y → S = R := star_55_12 x y
/-- ✱55·123. A relation is the indicated section-value iff it is the couple. -/
theorem star_55_123 (R : Rel α) (x y : α) : R = (fun z => pair z y) x ↔ R = pair x y := Iff.rfl
/-- ✱55·132. The couple relates its first constituent to its second. -/
theorem star_55_132 (x y : α) : pair x y x y := ⟨rfl,rfl⟩
/-- ✱55·134. Every ordinal couple is inhabited. -/
theorem star_55_134 (x y : α) : ∃ a b, pair x y a b := ⟨x,y,rfl,rfl⟩
/-- ✱55·14. Reversal of a couple is its converse. -/
theorem star_55_14 (x y : α) : pair x y = converse (pair y x) := by
  apply rel_ext; intro a b; simp [pair,cross,singleton,converse,and_comm]
/-- ✱55·15. Domain, converse-domain, and field of a couple. -/
theorem star_55_15 (x y : α) :
    domain (pair x y) = singleton x ∧ codomain (pair x y) = singleton y ∧
      field (pair x y) = fun z => z=x ∨ z=y := by
  refine ⟨class_ext (fun z => ?_), class_ext (fun z => ?_), class_ext (fun z => ?_)⟩
  · simp [domain,pair,cross,singleton]
  · simp [codomain,pair,cross,singleton]
  · simp [field,domain,codomain,pair,cross,singleton]

private theorem pair_of_domain_codomain {R : Rel α} {x y : α}
    (hu : ∃ a b, R = pair a b) (hd : domain R = singleton x)
    (hc : codomain R = singleton y) : R = pair x y := by
  rcases hu with ⟨a,b,rfl⟩
  have ha : a=x := by
    have : singleton x a := by rw [←hd]; exact ⟨b,rfl,rfl⟩
    exact this
  have hb : b=y := by
    have : singleton y b := by rw [←hc]; exact ⟨a,rfl,rfl⟩
    exact this
  subst a; subst b; rfl

/-- ✱55·16. Among ordinal couples, domain and converse-domain characterize it. -/
theorem star_55_16 (R : Rel α) (x y : α) (hu : ∃ a b, R=pair a b) :
    (domain R=singleton x ∧ codomain R=singleton y) ↔ R=pair x y := by
  constructor
  · rintro ⟨hd,hc⟩; exact pair_of_domain_codomain hu hd hc
  · rintro rfl; exact ⟨(star_55_15 x y).1,(star_55_15 x y).2.1⟩
/-- ✱55·161. The couple is the unique ordinal couple with these two projections. -/
theorem star_55_161 (x y : α) :
    ∃ R : Rel α, ((∃ a b, R=pair a b) ∧ domain R=singleton x ∧ codomain R=singleton y) ∧
      ∀ S, ((∃ a b, S=pair a b) ∧ domain S=singleton x ∧ codomain S=singleton y) → S=R := by
  refine ⟨pair x y, ⟨⟨x,y,rfl⟩,(star_55_15 x y).1,(star_55_15 x y).2.1⟩, ?_⟩
  rintro S ⟨hu,hd,hc⟩; exact pair_of_domain_codomain hu hd hc
/-- ✱55·17. Equivalent inverse-image characterization. -/
theorem star_55_17 (x y : α) :
    (fun R : Rel α => (∃ a b, R=pair a b) ∧ domain R=singleton x ∧ codomain R=singleton y) =
      (fun R => R=pair x y) := by
  funext R; apply propext; constructor
  · rintro ⟨hu,hd,hc⟩; exact pair_of_domain_codomain hu hd hc
  · rintro rfl; exact ⟨⟨x,y,rfl⟩,(star_55_15 x y).1,(star_55_15 x y).2.1⟩
/-- ✱55·2. Right cancellation for ordinal couples. -/
theorem star_55_2 (x y z : α) : pair x y=pair x z ↔ y=z := by
  constructor
  · intro h
    have q : pair x z x y := by rw [←h]; exact ⟨rfl,rfl⟩
    simpa [pair,cross,singleton] using q.2
  · rintro rfl; rfl
/-- ✱55·201. Left cancellation for ordinal couples. -/
theorem star_55_201 (x y z : α) : pair x z=pair y z ↔ x=y := by
  constructor
  · intro h
    have q : pair y z x z := by rw [←h]; exact ⟨rfl,rfl⟩
    simpa [pair,cross,singleton] using q.1
  · rintro rfl; rfl

end PM.Architecture.Star55OpeningKernel
