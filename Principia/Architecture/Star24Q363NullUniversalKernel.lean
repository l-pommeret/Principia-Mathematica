/-!
# PM I ✱24·17 and ✱24·21–24

Exact typed-class complement, null-class, and universal-class laws.  The
mathematically and contextually forced reading of ✱24·21 is `α ∩ −α = Λ`;
the repository's current plain-text locus has misread the printed `Λ` as `V`.
-/

namespace PM.Architecture.Star24Q363NullUniversalKernel

abbrev TypedClass (α : Sort _) := α → Prop

def inter (a b : TypedClass α) : TypedClass α := fun x => a x ∧ b x
def union (a b : TypedClass α) : TypedClass α := fun x => a x ∨ b x
def compl (a : TypedClass α) : TypedClass α := fun x => ¬ a x
def universal : TypedClass α := fun _ => True
def null : TypedClass α := fun _ => False

/-- ✱24·17. A class is universal exactly when its complement is null. -/
theorem star_24_17 (a : TypedClass α) :
    a = universal ↔ compl a = null := by
  constructor
  · rintro rfl
    funext x
    apply propext
    exact ⟨fun h => h True.intro, False.elim⟩
  · intro h
    funext x
    apply propext
    constructor
    · exact fun _ => True.intro
    · intro _
      exact Classical.byContradiction fun hna => by
        have : compl a x := hna
        have : null x := congrFun h x ▸ this
        exact this.elim

/-- ✱24·21, the law of contradiction: a class and its complement have null
intersection. -/
theorem star_24_21 (a : TypedClass α) :
    inter a (compl a) = null := by
  funext x
  apply propext
  exact ⟨fun h => h.2 h.1, False.elim⟩

/-- ✱24·22, excluded middle: a class together with its complement is the
universal class. -/
theorem star_24_22 (a : TypedClass α) :
    union a (compl a) = universal := by
  funext x
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Classical.em (a x)⟩

/-- ✱24·23. Intersection with the null class is null. -/
theorem star_24_23 (a : TypedClass α) :
    inter a null = null := by
  funext x
  apply propext
  exact ⟨fun h => h.2, False.elim⟩

/-- ✱24·24. Union with the null class leaves a class unchanged. -/
theorem star_24_24 (a : TypedClass α) :
    union a null = a := by
  funext x
  apply propext
  exact ⟨fun h => h.elim id False.elim, Or.inl⟩

end PM.Architecture.Star24Q363NullUniversalKernel
