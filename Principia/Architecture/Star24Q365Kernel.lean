/-! # PM I, ✱24·31–✱24·32: exact polymorphic class propositions. -/

namespace PM.Architecture.Star24Q365Kernel

abbrev Class (Object : Sort u) := Object → Prop
def Included (a b : Class Object) : Prop := ∀ x, a x → b x
def Union (a b : Class Object) : Class Object := fun x => a x ∨ b x
def Inter (a b : Class Object) : Class Object := fun x => a x ∧ b x
def Compl (a : Class Object) : Class Object := fun x => ¬ a x
def Diff (a b : Class Object) : Class Object := Inter a (Compl b)
def Universal : Class Object := fun _ => True
def Null : Class Object := fun _ => False

theorem class_ext {a b : Class Object} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x
  exact propext (h x)

/-- ✱24·31. Inclusion iff complement-union is universal. -/
theorem star_24_31 (a b : Class Object) :
    Included a b ↔ Union (Compl a) b = Universal := by
  classical
  constructor
  · intro h
    apply class_ext
    intro x
    constructor
    · exact fun _ => True.intro
    · intro _
      by_cases ha : a x
      · exact Or.inr (h x ha)
      · exact Or.inl ha
  · intro h x ha
    have hx : Compl a x ∨ b x := by
      have := congrFun h x
      rw [Union, Universal] at this
      exact this.symm.mp True.intro
    exact hx.resolve_left (fun hna => hna ha)

/-- ✱24·311. Inclusion in a complement iff the intersection is null. -/
theorem star_24_311 (a b : Class Object) :
    Included a (Compl b) ↔ Inter a b = Null := by
  constructor
  · intro h
    apply class_ext
    intro x
    constructor
    · rintro ⟨ha, hb⟩
      exact (h x ha) hb
    · exact False.elim
  · intro h x ha hb
    have : Inter a b x := ⟨ha, hb⟩
    rw [h] at this
    exact this

/-- ✱24·312. A complement included in `b` iff their union is universal. -/
theorem star_24_312 (a b : Class Object) :
    Included (Compl a) b ↔ Union a b = Universal := by
  classical
  constructor
  · intro h
    apply class_ext
    intro x
    constructor
    · exact fun _ => True.intro
    · intro _
      by_cases ha : a x
      · exact Or.inl ha
      · exact Or.inr (h x ha)
  · intro h x hna
    have hx : a x ∨ b x := by
      have := congrFun h x
      rw [Union, Universal] at this
      exact this.symm.mp True.intro
    exact hx.resolve_left hna

/-- ✱24·313. Disjointness iff subtracting `b` leaves `a`. -/
theorem star_24_313 (a b : Class Object) :
    Inter a b = Null ↔ a = Diff a b := by
  constructor
  · intro h
    apply class_ext
    intro x
    constructor
    · intro ha
      refine ⟨ha, fun hb => ?_⟩
      have : Inter a b x := ⟨ha, hb⟩
      rw [h] at this
      exact this
    · exact And.left
  · intro h
    apply class_ext
    intro x
    constructor
    · rintro ⟨ha, hb⟩
      have hd : Diff a b x := by rw [← h]; exact ha
      exact hd.2 hb
    · exact False.elim

/-- ✱24·32. A union is null iff both operands are null. -/
theorem star_24_32 (a b : Class Object) :
    Union a b = Null ↔ (a = Null ∧ b = Null) := by
  constructor
  · intro h
    constructor
    · apply class_ext
      intro x
      constructor
      · intro ha
        have : Union a b x := Or.inl ha
        rw [h] at this
        exact this
      · exact False.elim
    · apply class_ext
      intro x
      constructor
      · intro hb
        have : Union a b x := Or.inr hb
        rw [h] at this
        exact this
      · exact False.elim
  · rintro ⟨rfl, rfl⟩
    apply class_ext
    intro x
    exact ⟨fun h => h.elim False.elim False.elim, False.elim⟩

end PM.Architecture.Star24Q365Kernel
