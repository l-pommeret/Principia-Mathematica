/-!
# PM I ✱22·5, ✱22·51–54

Exact typed-class readings of the five displayed propositions. A class is its
membership predicate; intersection and inclusion retain the explicit common
member type.
-/

namespace PM.Architecture.Star22Q350IntersectionKernel

abbrev TypedClass (α : Sort _) := α → Prop

def inter (a b : TypedClass α) : TypedClass α :=
  fun x => a x ∧ b x

def subset (a b : TypedClass α) : Prop :=
  ∀ x, a x → b x

/-- ✱22·5. Intersection is idempotent. -/
theorem star_22_5 (a : TypedClass α) : inter a a = a := by
  funext x
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- ✱22·51. Intersection is commutative. -/
theorem star_22_51 (a b : TypedClass α) : inter a b = inter b a := by
  funext x
  apply propext
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- ✱22·52. Intersection is associative with the displayed bracketing. -/
theorem star_22_52 (a b c : TypedClass α) :
    inter (inter a b) c = inter a (inter b c) := by
  funext x
  apply propext
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The bracket-avoiding notation fixed by ✱22·53. -/
def tripleInter (a b c : TypedClass α) : TypedClass α :=
  inter (inter a b) c

/-- ✱22·53. The unbracketed triple product is left-associated. -/
theorem star_22_53 (a b c : TypedClass α) :
    tripleInter a b c = inter (inter a b) c := by
  rfl

/-- ✱22·54. Equality permits substitution in the left argument of class
inclusion, preserving both directions of the displayed equivalence. -/
theorem star_22_54 (a b c : TypedClass α) :
    a = b → (subset a c ↔ subset b c) := by
  rintro rfl
  exact Iff.rfl

end PM.Architecture.Star22Q350IntersectionKernel
