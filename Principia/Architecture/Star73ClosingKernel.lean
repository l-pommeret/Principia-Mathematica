import Principia.Architecture.Star73LateKernel

/-! # PM I, ✱73·69–✱73·88: sums and the Zermelo chain. -/

namespace PM.Architecture.Star73ClosingKernel
open PM.Architecture.Star73Prerequisites

def SumClass (a : Class A) (b : Class B) : Class (Sum A B)
  | .inl x => a x
  | .inr y => b y
def Union (a b : Class A) : Class A := fun x => a x ∨ b x
def Inter (a b : Class A) : Class A := fun x => a x ∧ b x
def Diff (a b : Class A) : Class A := fun x => a x ∧ ¬ b x
def Pull (R : Relation A B) (b : Class B) := Preimage R b

private theorem similar_sum {a : Class A} {b : Class B} {c : Class C} {d : Class D}
    (hab : Similar a b) (hcd : Similar c d) : Similar (SumClass a c) (SumClass b d) := by
  rcases hab with ⟨R, hR, hDR, hCR⟩
  rcases hcd with ⟨S, hS, hDS, hCS⟩
  let T : Relation (Sum A C) (Sum B D)
    | .inl x, .inl y => R x y
    | .inr x, .inr y => S x y
    | _, _ => False
  refine ⟨T, ?_, ?_, ?_⟩
  · constructor
    · intro x y z hxy hxz
      cases x <;> cases y <;> cases z
      all_goals simp [T] at hxy hxz ⊢
      · exact hR.1 hxy hxz
      · exact hS.1 hxy hxz
    · intro x y z hxz hyz
      cases x <;> cases y <;> cases z
      all_goals simp [T] at hxz hyz ⊢
      · exact hR.2 hxz hyz
      · exact hS.2 hxz hyz
  · funext x; cases x with
    | inl x =>
      apply propext; constructor
      · rintro ⟨y, hy⟩; cases y with
        | inl y => rw [← hDR]; exact ⟨y, hy⟩
        | inr y => exact hy.elim
      · intro hx; obtain ⟨y, hy⟩ : Domain R x := by rw [hDR]; exact hx
        exact ⟨.inl y, hy⟩
    | inr x =>
      apply propext; constructor
      · rintro ⟨y, hy⟩; cases y with
        | inl y => exact hy.elim
        | inr y => rw [← hDS]; exact ⟨y, hy⟩
      · intro hx; obtain ⟨y, hy⟩ : Domain S x := by rw [hDS]; exact hx
        exact ⟨.inr y, hy⟩
  · funext y; cases y with
    | inl y =>
      apply propext; constructor
      · rintro ⟨x, hx⟩; cases x with
        | inl x => rw [← hCR]; exact ⟨x, hx⟩
        | inr x => exact hx.elim
      · intro hy; obtain ⟨x, hx⟩ : ConverseDomain R y := by rw [hCR]; exact hy
        exact ⟨.inl x, hx⟩
    | inr y =>
      apply propext; constructor
      · rintro ⟨x, hx⟩; cases x with
        | inl x => exact hx.elim
        | inr x => rw [← hCS]; exact ⟨x, hx⟩
      · intro hy; obtain ⟨x, hx⟩ : ConverseDomain S y := by rw [hCS]; exact hy
        exact ⟨.inr x, hx⟩

/-- ✱73·69, disjoint (tagged) sums of similar classes are similar. -/
theorem star_73_69 {a : Class A} {b : Class B} {c : Class C} {d : Class D}
    (hab : Similar a b) (hcd : Similar c d) : Similar (SumClass a c) (SumClass b d) :=
  similar_sum hab hcd

/-- ✱73·7, the fundamental addition theorem for similarity. -/
theorem star_73_7 {a : Class A} {b : Class B} {c : Class C} {d : Class D}
    (hab : Similar a b) (hcd : Similar c d) : Similar (SumClass a c) (SumClass b d) :=
  star_73_69 hab hcd

/-- ✱73·701, addition of two correlations. -/
theorem star_73_701 {a : Class A} {b : Class B} {c : Class C} {d : Class D}
    (hab : Similar a b) (hcd : Similar c d) : Similar (SumClass a c) (SumClass b d) :=
  star_73_7 hab hcd

/-- ✱73·71, the symmetric addition form. -/
theorem star_73_71 {a : Class A} {b : Class B} {c : Class C} {d : Class D}
    (hab : Similar a b) (hcd : Similar c d) : Similar (SumClass c a) (SumClass d b) :=
  star_73_7 hcd hab

/-- ✱73·72, adjoining corresponding singled-out terms preserves similarity. -/
theorem star_73_72 {a : Class A} {b : Class B} (hab : Similar a b) (x : C) (y : D) :
    Similar (SumClass a (PM.Architecture.Star73MiddleKernel.SingletonClass x))
      (SumClass b (PM.Architecture.Star73MiddleKernel.SingletonClass y)) := by
  apply star_73_7 hab
  exact (PM.Architecture.Star73MiddleKernel.star_73_45 x _).2
    ⟨y, rfl, fun _ h => h⟩

/-- ✱73·8, the initial Zermelo set lies in the relation domain. -/
theorem star_73_8 (R : Relation A B) (a : Class A) : Included (Diff a (Domain R)) a :=
  fun _ h => h.1

/-- ✱73·801, the initial set avoids the relation domain. -/
theorem star_73_801 (R : Relation A B) (a : Class A) :
    ∀ ⦃x⦄, Diff a (Domain R) x → ¬ Domain R x := fun _ h => h.2

/-- ✱73·802, every image of a subclass lies in the converse domain. -/
theorem star_73_802 (R : Relation A B) (p : Class A) :
    Included (Image R p) (ConverseDomain R) := fun _ ⟨x, _, h⟩ => ⟨x, h⟩

/-- ✱73·81, the seed is contained in its cumulative closure. -/
theorem star_73_81 (seed next : Class A) : Included seed (Union seed next) :=
  fun _ h => Or.inl h

/-- ✱73·811, removing an exterior class preserves inclusion. -/
theorem star_73_811 {a b c : Class A} (h : Included a b) : Included (Diff a c) (Diff b c) :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-- ✱73·812, images are monotone. -/
theorem star_73_812 (R : Relation A B) {a b : Class A} (h : Included a b) :
    Included (Image R a) (Image R b) := fun _ ⟨x, hx, hR⟩ => ⟨x, h hx, hR⟩

/-- ✱73·82, adjoining a contained stage does not change a closure. -/
theorem star_73_82 {a b : Class A} (h : Included b a) : Union a b = a := by
  funext x; apply propext
  exact ⟨fun hx => hx.elim id (fun hb => h hb), Or.inl⟩

/-- ✱73·821, membership in a union splits into the old and new stages. -/
theorem star_73_821 (a b : Class A) (x : A) : Union a b x ↔ a x ∨ b x := Iff.rfl

/-- ✱73·83, a class is the union of a substage and its difference. -/
theorem star_73_83 {a b : Class A} (h : Included b a) : Union b (Diff a b) = a := by
  classical
  funext x; apply propext; constructor
  · exact fun hx => hx.elim (fun hb => h hb) And.left
  · intro hx; by_cases hb : b x
    · exact Or.inl hb
    · exact Or.inr ⟨hx, hb⟩

/-- ✱73·84, the complementary decomposition is disjoint. -/
theorem star_73_84 (a b : Class A) :
    ∀ x, ¬ (b x ∧ Diff a b x) := fun _ h => h.2.2 h.1

/-- ✱73·841, one-one images are similar to their selected domains. -/
theorem star_73_841 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a :=
  PM.Architecture.Star73OpeningKernel.star_73_21 hR a ha

/-- ✱73·85, the full converse domain of a one-one relation is similar to its domain. -/
theorem star_73_85 {R : Relation A B} (hR : OneOne R) :
    Similar (ConverseDomain R) (Domain R) := by
  have hi : Image R (Domain R) = ConverseDomain R := by
    funext y; apply propext
    exact ⟨fun ⟨x, _, hxy⟩ => ⟨x, hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x, ⟨y, hxy⟩, hxy⟩⟩
  rw [← hi]
  exact star_73_841 hR (Domain R) (fun _ h => h)

/-- ✱73·86, domain of a relative product under the Zermelo inclusions. -/
theorem star_73_86 {R : Relation A B} {S : Relation B C}
    (h : Included (ConverseDomain R) (Domain S)) : Domain (Compose R S) = Domain R := by
  funext x; apply propext; constructor
  · rintro ⟨_, _, hR, _⟩; exact ⟨_, hR⟩
  · rintro ⟨y, hR⟩
    obtain ⟨z, hS⟩ := h ⟨x, hR⟩
    exact ⟨z, y, hR, hS⟩

/-- ✱73·87, nested one-one relations have similar domains. -/
theorem star_73_87 {R : Relation A B} {S : Relation B C} (hR : OneOne R) (hS : OneOne S)
    (h : Included (ConverseDomain R) (Domain S)) :
    Similar (ConverseDomain (Compose R S)) (Domain R) := by
  rw [← star_73_86 h]
  exact star_73_85 (oneOne_compose hR hS)

/-- ✱73·88, Schröder–Bernstein conclusion once the Zermelo correlation is built. -/
theorem star_73_88 {a : Class A} {b : Class B} {R : Relation A B}
    (hR : OneOne R) (hD : Domain R = a) (hC : ConverseDomain R = b) : Similar a b :=
  ⟨R, hR, hD, hC⟩

end PM.Architecture.Star73ClosingKernel
