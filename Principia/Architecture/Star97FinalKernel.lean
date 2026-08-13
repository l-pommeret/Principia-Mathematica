/-! Reachability kernel for the final propositions of PM I ✱97. -/
namespace PM.Architecture.Star97FinalKernel

abbrev Rel (α : Type u) := α → α → Prop
inductive Reach (R : Rel α) : α → α → Prop
  | refl (x) : Reach R x x
  | tail {x y z} : Reach R x y → R y z → Reach R x z
def sameFamily (R : Rel α) (x y : α) : Prop := Reach R x y ∨ Reach R y x
def functional (R : Rel α) : Prop := ∀ ⦃x y z⦄, R x y → R x z → y = z
def injective (R : Rel α) : Prop := ∀ ⦃x y z⦄, R x z → R y z → x = y
def fixed (R : Rel α) (x : α) : Prop := R x x

theorem reach_trans (R : Rel α) {x y z : α} : Reach R x y → Reach R y z → Reach R x z := by
  intro hxy hyz
  induction hyz with
  | refl => exact hxy
  | tail _ hr ih => exact .tail ih hr

theorem star_97_44 (R : Rel α) {x y z : α}
    (hxy : Reach R x y) (hyz : Reach R y z) : Reach R x z := reach_trans R hxy hyz

theorem star_97_45 (R : Rel α) {x y : α} (h : sameFamily R x y) :
    sameFamily R y x := h.elim Or.inr Or.inl

theorem star_97_501 (R : Rel α) (hf : injective R) {x y : α}
    (hxx : R x x) (hyx : R y x) : x = y := by
  exact hf hxx hyx

theorem star_97_51 (R : Rel α) (hi : functional R) {x y : α}
    (hxx : R x x) (hxy : R x y) : x = y := hi hxx hxy

theorem star_97_52 (R : Rel α) {x y : α} (h : Reach R x y) :
    sameFamily R x y := Or.inl h

theorem star_97_53 (R : Rel α) {x y : α} (hxx : fixed R x)
    (h : sameFamily R x y) : fixed R x ∧ sameFamily R y x :=
  ⟨hxx, h.elim Or.inr Or.inl⟩

theorem star_97_56 (R : Rel α) {x y : α} (h : sameFamily R x y) :
    sameFamily R x x ∧ sameFamily R y y :=
  ⟨Or.inl (.refl x), Or.inl (.refl y)⟩

end PM.Architecture.Star97FinalKernel
