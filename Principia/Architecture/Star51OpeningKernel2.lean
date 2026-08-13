import Principia.Architecture.Star51OpeningKernel

namespace PM.Architecture.Star51OpeningKernel2

open PM.Architecture.Star51OpeningKernel

def Included (A B : Class α) : Prop := ∀ x, A x → B x
def Intersection (A B : Class α) : Class α := fun x => A x ∧ B x
def Union (A B : Class α) : Class α := fun x => A x ∨ B x
def Difference (A B : Class α) : Class α := fun x => A x ∧ ¬B x
def Null : Class α := fun _ => False
def Universal : Class α := fun _ => True

/-- ✱51·161: the unit class is existent. -/
theorem star_51_161 (x : α) : ClassExists (singleton x) := by
  exact ⟨x, rfl⟩

/-- ✱51·17: every object lies in the converse domain of `ι`. -/
theorem star_51_17 :
    (fun x : α => ∃ A : Class α, iotaRelation A x) = Universal := by
  funext x
  apply propext
  exact ⟨fun _ => True.intro, fun _ => ⟨singleton x, rfl⟩⟩

/-- ✱51·2: membership is inclusion of the corresponding unit class. -/
theorem star_51_2 (x : α) (A : Class α) :
    A x ↔ Included (singleton x) A := by
  exact ⟨fun hx _ hy => hy ▸ hx, fun h => h x rfl⟩

/-- ✱51·21: removing `ιʻx` leaves `x` outside. -/
theorem star_51_21 (x : α) (A : Class α) :
    ¬Difference A (singleton x) x := by
  rintro ⟨_, h⟩
  exact h rfl

/-- ✱51·211: non-membership is disjointness from the unit class. -/
theorem star_51_211 (x : α) (A : Class α) :
    ¬A x ↔ Intersection (singleton x) A = Null := by
  constructor
  · intro h
    funext y
    apply propext
    exact ⟨fun hy => h (hy.1 ▸ hy.2), False.elim⟩
  · intro h hx
    have : Null x := by rw [← h]; exact ⟨rfl, hx⟩
    exact this

/-- ✱51·22: removing an adjoined fresh unit recovers the original class. -/
theorem star_51_22 (x : α) (A B : Class α) :
    (Intersection A (singleton x) = Null ∧ Union A (singleton x) = B) ↔
      (B x ∧ A = Difference B (singleton x)) := by
  classical
  constructor
  · rintro ⟨hdisjoint, hunion⟩
    constructor
    · rw [← hunion]
      exact Or.inr rfl
    · funext y
      apply propext
      constructor
      · intro ha
        refine ⟨?_, ?_⟩
        · rw [← hunion]; exact Or.inl ha
        · intro hyx
          have : Null y := by rw [← hdisjoint]; exact ⟨ha, hyx⟩
          exact this
      · rintro ⟨hb, _⟩
        rw [← hunion] at hb
        exact hb.resolve_right ‹¬singleton x y›
  · rintro ⟨hbx, rfl⟩
    constructor
    · funext y
      apply propext
      exact ⟨fun h => h.1.2 h.2, False.elim⟩
    · funext y
      apply propext
      constructor
      · rintro (⟨hb, _⟩ | hyx)
        · exact hb
        · exact hyx ▸ hbx
      · intro hb
        by_cases hyx : y = x
        · exact Or.inr hyx
        · exact Or.inl ⟨hb, hyx⟩

/-- ✱51·221: deleting and then restoring a member leaves the class fixed. -/
theorem star_51_221 (x : α) (A : Class α) :
    A x ↔ Union (Difference A (singleton x)) (singleton x) = A := by
  classical
  constructor
  · intro hx
    funext y
    apply propext
    exact ⟨fun h => h.elim And.left (fun hyx => hyx ▸ hx),
      fun hy => if h : y = x then Or.inr h else Or.inl ⟨hy, h⟩⟩
  · intro h
    rw [← h]
    exact Or.inr rfl

/-- ✱51·222: deleting a non-member changes nothing. -/
theorem star_51_222 (x : α) (A : Class α) :
    ¬A x ↔ Difference A (singleton x) = A := by
  constructor
  · intro hx
    funext y
    apply propext
    exact ⟨And.left, fun hy => ⟨hy, fun hyx => hx (hyx ▸ hy)⟩⟩
  · intro h hx
    have : Difference A (singleton x) x := by rw [h]; exact hx
    exact this.2 rfl

/-- ✱51·23: the four printed unit-class identity conditions agree. -/
theorem star_51_23 (x y : α) :
    (singleton x = singleton y ↔ singleton x y) ∧
    (singleton x y ↔ singleton y x) ∧
    (singleton y x ↔ x = y) := by
  constructor
  · constructor
    · intro h
      rw [h]
      rfl
    · intro hyx
      subst y
      rfl
  · exact ⟨⟨Eq.symm, Eq.symm⟩, Iff.rfl⟩

/-- ✱51·231: two unit classes are disjoint exactly when their elements
differ. -/
theorem star_51_231 (x y : α) :
    Intersection (singleton x) (singleton y) = Null ↔ x ≠ y := by
  constructor
  · intro h hxy
    subst y
    have : Null x := by rw [← h]; exact ⟨rfl, rfl⟩
    exact this
  · intro h
    funext z
    apply propext
    exact ⟨fun hz => h (hz.1.symm.trans hz.2), False.elim⟩

end PM.Architecture.Star51OpeningKernel2
