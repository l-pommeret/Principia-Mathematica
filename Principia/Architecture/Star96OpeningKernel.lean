import Principia.Architecture.Star96Prerequisites
import Principia.FirstEdition.Volume1.Star96Source

namespace PM.Architecture.Star96OpeningKernel
open PM.Architecture.Star96Prerequisites

def Ipart (R : Relation α) (x : α) : Class α :=
  fun z => ReflexiveClosure R x z ∧ TransitiveClosure R z z
def Jpart (R : Relation α) (x : α) : Class α :=
  fun z => ReflexiveClosure R x z ∧ ¬ Ipart R x z

theorem star_96_01 : Ipart R x = fun z => ReflexiveClosure R x z ∧ TransitiveClosure R z z := rfl
theorem star_96_02 : Jpart R x = fun z => ReflexiveClosure R x z ∧ ¬ Ipart R x z := rfl
theorem star_96_1 : Ipart R x z ↔ ReflexiveClosure R x z ∧ TransitiveClosure R z z := Iff.rfl
theorem star_96_101 : Jpart R x z ↔ ReflexiveClosure R x z ∧ ¬ TransitiveClosure R z z := by
  constructor
  · rintro ⟨hr, hn⟩; exact ⟨hr, fun ht => hn ⟨hr,ht⟩⟩
  · rintro ⟨hr, hn⟩; exact ⟨hr, fun hi => hn hi.2⟩
theorem star_96_102_union :
    (fun z => Jpart R x z ∨ Ipart R x z) = converseImage (ReflexiveClosure R) x := by
  classical
  funext z; apply propext; constructor
  · rintro (h | h) <;> exact h.1
  · intro hr
    by_cases ht : TransitiveClosure R z z
    · exact Or.inr ⟨hr,ht⟩
    · exact Or.inl ⟨hr, fun hi => ht hi.2⟩
theorem star_96_102_disjoint : ¬ ∃ z, Jpart R x z ∧ Ipart R x z := by
  rintro ⟨z,hJ,hI⟩; exact hJ.2 hI

/-- The two displayed conjuncts of PM ✱96·102, kept together under the
canonical theorem name. -/
theorem star_96_102 :
    converseImage (ReflexiveClosure R) x =
        (fun z => Jpart R x z ∨ Ipart R x z) ∧
      (fun z => Jpart R x z ∧ Ipart R x z) = (fun _ => False) := by
  constructor
  · exact star_96_102_union.symm
  · funext z
    apply propext
    exact ⟨fun h => star_96_102_disjoint ⟨z, h⟩, False.elim⟩

theorem star_96_103 :
    IncludedRelation (restrictDomain (Jpart R x) (TransitiveClosure R)) Diversity := by
  rintro z y ⟨hz, hzy⟩ equality
  subst y
  exact hz.2 ⟨hz.1, hzy⟩

theorem star_96_104 :
    Ipart R x = (fun _ => False) ↔
      IncludedRelation (restrictDomain (converseImage (ReflexiveClosure R) x)
        (TransitiveClosure R)) Diversity := by
  constructor
  · intro empty z y h equality
    subst y
    have hi : Ipart R x z := ⟨h.1, h.2⟩
    have := congrFun empty z
    exact Eq.mp this hi
  · intro h
    funext z; apply propext; constructor
    · intro hi
      exact h ⟨hi.1,hi.2⟩ rfl
    · exact False.elim

theorem tc_restrictDomain_included :
    IncludedRelation (TransitiveClosure (restrictDomain A R))
      (restrictDomain A (TransitiveClosure R)) := by
  intro x y h
  induction h with
  | single h => exact ⟨h.1, .single h.2⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1, .trans ih₁.2 ih₂.2⟩

theorem star_96_11 :
    IncludedRelation (TransitiveClosure (restrictDomain A R))
      (restrictDomain A (TransitiveClosure R)) := tc_restrictDomain_included

theorem tc_restrictRange_included :
    IncludedRelation (TransitiveClosure (restrictRange R A))
      (restrictRange (TransitiveClosure R) A) := by
  intro x y h
  induction h with
  | single h => exact ⟨.single h.1, h.2⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨.trans ih₁.1 ih₂.1, ih₂.2⟩

def ForwardClosed (A : Class α) (R : Relation α) :=
  ∀ {x y}, A x → R x y → A y
def BackwardClosed (A : Class α) (R : Relation α) :=
  ∀ {x y}, A y → R x y → A x

theorem forwardClosed_tc (h : ForwardClosed A R) :
    A x → TransitiveClosure R x y → A y := by
  intro hx htc; induction htc with
  | single e => exact h hx e
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)

theorem backwardClosed_tc (h : BackwardClosed A R) :
    A y → TransitiveClosure R x y → A x := by
  intro hy htc; induction htc with
  | single e => exact h hy e
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hy)

theorem star_96_111 (closed : ForwardClosed A R) :
    TransitiveClosure (restrictDomain A R) = restrictDomain A (TransitiveClosure R) := by
  funext x y; apply propext; refine ⟨tc_restrictDomain_included, ?_⟩
  rintro ⟨hA,h⟩
  induction h with
  | single hxy => exact .single ⟨hA,hxy⟩
  | trans hxy hyz ihxy ihyz =>
      exact .trans (ihxy hA) (ihyz (forwardClosed_tc closed hA hxy))

theorem star_96_121 (closed : BackwardClosed A R) :
    TransitiveClosure (restrictRange R A) = restrictRange (TransitiveClosure R) A := by
  funext x y; apply propext; refine ⟨tc_restrictRange_included, ?_⟩
  rintro ⟨h,hA⟩
  induction h with
  | single hxy => exact .single ⟨hxy,hA⟩
  | @trans p q r hxy hyz ihxy ihyz =>
      have mid : A q := backwardClosed_tc (R := R) closed hA hyz
      exact .trans (ihxy mid) (ihyz hA)

theorem field_restrictDomain :
    field (restrictDomain A R) = fun z =>
      (A z ∧ domain R z) ∨ ∃ x, A x ∧ R x z := by
  funext z; apply propext
  exact ⟨fun h => match h with
    | Or.inl ⟨y,hA,hR⟩ => Or.inl ⟨hA,⟨y,hR⟩⟩
    | Or.inr ⟨x,hA,hR⟩ => Or.inr ⟨x,hA,hR⟩,
    fun h => match h with
    | Or.inl ⟨hA,⟨y,hR⟩⟩ => Or.inl ⟨y,hA,hR⟩
    | Or.inr ⟨x,hA,hR⟩ => Or.inr ⟨x,hA,hR⟩⟩

theorem field_restrictRange :
    field (restrictRange R A) = fun z =>
      (∃ y, R z y ∧ A y) ∨ (range R z ∧ A z) := by
  funext z; apply propext
  exact ⟨fun h => match h with
    | Or.inl ⟨y,hR,hA⟩ => Or.inl ⟨y,hR,hA⟩
    | Or.inr ⟨x,hR,hA⟩ => Or.inr ⟨⟨x,hR⟩,hA⟩,
    fun h => match h with
    | Or.inl ⟨y,hR,hA⟩ => Or.inl ⟨y,hR,hA⟩
    | Or.inr ⟨⟨x,hR⟩,hA⟩ => Or.inr ⟨x,hR,hA⟩⟩

theorem star_96_14 :
    field R x →
    converseImage (ReflexiveClosure R) x =
      fun z => z = x ∨ converseImage (TransitiveClosure R) x z := by
  intro hf
  funext z; apply propext
  simp [converseImage, ReflexiveClosure, eq_comm, hf]

end PM.Architecture.Star96OpeningKernel
