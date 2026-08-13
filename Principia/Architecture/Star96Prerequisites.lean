namespace PM.Architecture.Star96Prerequisites

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) := α → α → Prop

inductive TransitiveClosure (R : Relation α) : Relation α
  | single {x y} : R x y → TransitiveClosure R x y
  | trans {x y z} : TransitiveClosure R x y → TransitiveClosure R y z → TransitiveClosure R x z

def converseImage (R : Relation α) (x : α) : Class α := fun z => R x z
def domain (R : Relation α) : Class α := fun x => ∃ y, R x y
def range (R : Relation α) : Class α := fun y => ∃ x, R x y
def field (R : Relation α) : Class α := fun x => domain R x ∨ range R x
def ReflexiveClosure (R : Relation α) : Relation α :=
  fun x y => (x = y ∧ field R x) ∨ TransitiveClosure R x y
def restrictDomain (A : Class α) (R : Relation α) : Relation α := fun x y => A x ∧ R x y
def restrictRange (R : Relation α) (A : Class α) : Relation α := fun x y => R x y ∧ A y
def relationClass (P : Relation α → Prop) : Class (Relation α) := P
def uniquelyDescribes (P : α → Prop) (x : α) := P x ∧ ∀ y, P y → y = x

/-- PM's class `J`, interpreted extensionally as well-founded relations.  `Acc`
uses incoming edges, matching PM's ancestral orientation. -/
def WellFoundedRelation (R : Relation α) : Prop := ∀ x, Acc R x
def J : Class (Relation α) := WellFoundedRelation
def Diversity : Relation α := fun x y => x ≠ y
def IncludedRelation (R S : Relation α) := ∀ {x y}, R x y → S x y

theorem wellFounded_restrictDomain {R : Relation α} (h : WellFoundedRelation R) (A : Class α) :
    WellFoundedRelation (restrictDomain A R) := by
  intro x
  induction h x with
  | intro x _ ih =>
      exact Acc.intro x (fun y hy => ih y hy.2)

theorem wellFounded_restrictRange {R : Relation α} (h : WellFoundedRelation R) (A : Class α) :
    WellFoundedRelation (restrictRange R A) := by
  intro x
  induction h x with
  | intro x _ ih =>
      exact Acc.intro x (fun y hy => ih y hy.1)

theorem domain_restrictDomain :
    domain (restrictDomain A R) = fun x => A x ∧ domain R x := by
  funext x; apply propext
  exact ⟨fun ⟨y,hA,hR⟩ => ⟨hA,⟨y,hR⟩⟩,
    fun ⟨hA,⟨y,hR⟩⟩ => ⟨y,hA,hR⟩⟩

theorem range_restrictRange :
    range (restrictRange R A) = fun y => range R y ∧ A y := by
  funext y; apply propext
  exact ⟨fun ⟨x,hR,hA⟩ => ⟨⟨x,hR⟩,hA⟩,
    fun ⟨⟨x,hR⟩,hA⟩ => ⟨x,hR,hA⟩⟩

theorem field_eq_union : field R = fun x => domain R x ∨ range R x := rfl

theorem tc_trans : TransitiveClosure R x y → TransitiveClosure R y z → TransitiveClosure R x z := by
  exact TransitiveClosure.trans

theorem tc_of_edge (h : R x y) : TransitiveClosure R x y := .single h
theorem rtc_refl (h : field R x) : ReflexiveClosure R x x := Or.inl ⟨rfl,h⟩
theorem tc_rtc (h : TransitiveClosure R x y) : ReflexiveClosure R x y := Or.inr h
theorem rtc_trans : ReflexiveClosure R x y → ReflexiveClosure R y z → ReflexiveClosure R x z := by
  rintro (⟨rfl,_⟩ | hxy) (⟨rfl,hf⟩ | hyz)
  · exact Or.inl ⟨rfl,hf⟩
  · exact Or.inr hyz
  · exact Or.inr hxy
  · exact Or.inr (tc_trans hxy hyz)

end PM.Architecture.Star96Prerequisites
