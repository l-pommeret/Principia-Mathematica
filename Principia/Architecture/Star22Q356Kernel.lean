import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q356Kernel

open PM.Architecture.Star22Q341Definitions

/-- ✱22·81: complementation reverses inclusion. -/
theorem star_22_81 (alpha beta : Class Object) :
    Included alpha beta ↔ Included (Complement beta) (Complement alpha) := by
  classical
  constructor
  · intro hab x hnb ha
    exact hnb (hab x ha)
  · intro h x ha
    apply Classical.byContradiction
    intro hnb
    exact h x hnb ha

/-- ✱22·811: inclusion in a complement is symmetric. -/
theorem star_22_811 (alpha beta : Class Object) :
    Included alpha (Complement beta) ↔ Included beta (Complement alpha) := by
  constructor
  · intro h x hb ha
    exact h x ha hb
  · intro h x ha hb
    exact h x hb ha

/-- ✱22·82: `α ∩ β ⊂ γ` iff `α − γ ⊂ −β`. -/
theorem star_22_82 (alpha beta gamma : Class Object) :
    Included (Intersection alpha beta) gamma ↔
      Included (Difference alpha gamma) (Complement beta) := by
  classical
  constructor
  · intro h x hx hb
    exact hx.2 (h x ⟨hx.1, hb⟩)
  · intro h x hx
    apply Classical.byContradiction
    intro hgc
    exact h x ⟨hx.1, hgc⟩ hx.2

/-- ✱22·83: equality is preserved and reflected by complementation. -/
theorem star_22_83 (alpha beta : Class Object) :
    alpha = beta ↔ Complement alpha = Complement beta := by
  classical
  constructor
  · rintro rfl
    rfl
  · intro h
    funext x
    apply propext
    constructor
    · intro ha
      apply Classical.byContradiction
      intro hnb
      have hna : Complement alpha x := by
        rw [h]
        exact hnb
      exact hna ha
    · intro hb
      apply Classical.byContradiction
      intro hna
      have hnb : Complement beta x := by
        rw [← h]
        exact hna
      exact hnb hb

/-- ✱22·831: being the complement of a class is a symmetric relation. -/
theorem star_22_831 (alpha beta : Class Object) :
    alpha = Complement beta ↔ beta = Complement alpha := by
  classical
  constructor
  · intro h
    funext x
    apply propext
    constructor
    · intro hb ha
      have hnb : ¬beta x := by simpa [h] using ha
      exact hnb hb
    · intro hna
      apply Classical.byContradiction
      intro hnb
      have ha : alpha x := by simpa [h] using hnb
      exact hna ha
  · intro h
    funext x
    apply propext
    constructor
    · intro ha hb
      have hna : ¬alpha x := by simpa [h] using hb
      exact hna ha
    · intro hnb
      apply Classical.byContradiction
      intro hna
      have hb : beta x := by simpa [h] using hna
      exact hnb hb

end PM.Architecture.Star22Q356Kernel
