/-! # PM I, ✱54·01–✱54·27: opening cardinal-couple propositions. -/

namespace PM.Architecture.Star54OpeningKernel

abbrev Class (Object : Sort u) := Object → Prop
abbrev CardinalClass (Object : Sort u) := Class Object → Prop

def Empty : Class Object := fun _ => False
def Singleton (x : Object) : Class Object := fun z => z = x
def Pair (x y : Object) : Class Object := fun z => z = x ∨ z = y
def Zero : CardinalClass Object := fun alpha => alpha = Empty
def One : CardinalClass Object := fun alpha => ∃ x, alpha = Singleton x
def Two : CardinalClass Object :=
  fun alpha => ∃ x y, x ≠ y ∧ alpha = Pair x y

theorem class_ext {alpha beta : Class Object}
    (h : ∀ x, alpha x ↔ beta x) : alpha = beta := by
  funext x
  exact propext (h x)

/-- ✱54·01. `0 = ιʻΛ` Df. -/
def star_54_01 : CardinalClass Object :=
  fun alpha => alpha = Empty

/-- ✱54·02. `2 = α̂{(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy}` Df. -/
def star_54_02 : CardinalClass Object :=
  fun alpha => ∃ x y, x ≠ y ∧ alpha = Pair x y

/-- ✱54·1 repeats the defining identity `0 = ιʻΛ`. -/
theorem star_54_1 : Zero = fun alpha : Class Object => alpha = Empty := rfl

/-- ✱54·101, membership in cardinal two. -/
theorem star_54_101 (alpha : Class Object) :
    Two alpha ↔ ∃ x y, x ≠ y ∧ alpha = Pair x y := Iff.rfl

/-- ✱54·102, membership in cardinal zero. -/
theorem star_54_102 (alpha : Class Object) : Zero alpha ↔ alpha = Empty := Iff.rfl

/-- ✱54·21, cancellation of a common member from cardinal couples. -/
theorem star_54_21 (x y z : Object) : Pair x y = Pair x z ↔ y = z := by
  classical
  constructor
  · intro h
    by_cases hy : y = x
    · subst y
      have hzOr : z = x ∨ z = z := Or.inr rfl
      have hxz : z = x := by
        have : Pair x x z := by rw [h]; exact hzOr
        exact this.elim id id
      exact hxz.symm
    · have hyMem : Pair x z y := by rw [← h]; exact Or.inr rfl
      exact hyMem.resolve_left hy
  · rintro rfl
    rfl

/-- ✱54·22, equality of couples gives equality in one of the two orders. -/
theorem star_54_22 (x y z w : Object) :
    Pair x y = Pair z w → ((x = z ∧ y = w) ∨ (x = w ∧ y = z)) := by
  classical
  intro h
  have hx : x = z ∨ x = w := by
    have : Pair z w x := by rw [← h]; exact Or.inl rfl
    exact this
  rcases hx with hxz | hxw
  · subst z
    exact Or.inl ⟨rfl, (star_54_21 x y w).mp h⟩
  · subst w
    have h' : Pair x y = Pair x z := by
      rw [h]
      apply class_ext
      intro a
      exact or_comm
    exact Or.inr ⟨rfl, (star_54_21 x y z).mp h'⟩

/-- ✱54·25, a couple is a unit class exactly when its members coincide. -/
theorem star_54_25 (x y : Object) : One (Pair x y) ↔ x = y := by
  constructor
  · rintro ⟨z, h⟩
    have hx : x = z := by
      have : Singleton z x := by rw [← h]; exact Or.inl rfl
      exact this
    have hy : y = z := by
      have : Singleton z y := by rw [← h]; exact Or.inr rfl
      exact this
    exact hx.trans hy.symm
  · rintro rfl
    refine ⟨x, ?_⟩
    apply class_ext
    intro z
    exact ⟨fun h => h.elim id id, Or.inl⟩

/-- ✱54·26, a couple belongs to cardinal two exactly when distinct. -/
theorem star_54_26 (x y : Object) : Two (Pair x y) ↔ x ≠ y := by
  constructor
  · rintro ⟨a, b, hab, h⟩ hxy
    subst y
    have hone : One (Pair x x) := (star_54_25 x x).mpr rfl
    obtain ⟨z, hz⟩ := hone
    have ha : a = z := by
      have : Singleton z a := by rw [← hz, h]; exact Or.inl rfl
      exact this
    have hb : b = z := by
      have : Singleton z b := by rw [← hz, h]; exact Or.inr rfl
      exact this
    exact hab (ha.trans hb.symm)
  · intro hxy
    exact ⟨x, y, hxy, rfl⟩

/-- ✱54·27, every cardinal couple belongs to cardinal one or two. -/
theorem star_54_27 (x y : Object) : One (Pair x y) ∨ Two (Pair x y) := by
  classical
  by_cases h : x = y
  · exact Or.inl ((star_54_25 x y).mpr h)
  · exact Or.inr ((star_54_26 x y).mpr h)

end PM.Architecture.Star54OpeningKernel
