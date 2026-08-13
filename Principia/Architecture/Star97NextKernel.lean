/-! Reachability kernel for PM I ✱97, second macro-lot. -/
namespace PM.Architecture.Star97NextKernel

abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def field (R : Rel α) : Set α := fun x => (∃ y, R x y) ∨ ∃ y, R y x
inductive Reach (R : Rel α) : α → α → Prop
  | refl (x) : Reach R x x
  | tail {x y z} : Reach R x y → R y z → Reach R x z
def sameFamily (R : Rel α) (x y : α) : Prop := Reach R x y ∨ Reach R y x
def root (R : Rel α) (x : α) : Prop := ¬∃ y, R y x
def closed (R : Rel α) (s : Set α) : Prop := ∀ ⦃x y⦄, s x → R x y → s y
def injectiveRel (R : Rel α) : Prop := ∀ ⦃x y z⦄, R x z → R y z → x = y
def functionalRel (R : Rel α) : Prop := ∀ ⦃x y z⦄, R x y → R x z → y = z

theorem star_97_241 (R : Rel α) (x : α) : sameFamily R x x := Or.inl (.refl x)
theorem star_97_242 (R : Rel α) {x y : α} : sameFamily R x y ↔ sameFamily R y x :=
  ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
theorem star_97_301 (R : Rel α) (x : α) : Reach R x x := .refl x
theorem star_97_32 (R : Rel α) (x : α) : ∃ y, Reach R x y := ⟨x, .refl x⟩

theorem star_97_33 (R : Rel α) {x y z : α} :
    Reach R x y → R y z → Reach R x z := Reach.tail

theorem reach_trans (R : Rel α) {x y z : α} : Reach R x y → Reach R y z → Reach R x z := by
  intro hxy hyz
  induction hyz with
  | refl => exact hxy
  | tail h _ ih => exact .tail ih ‹R _ _›

theorem star_97_34 (R : Rel α) {x y z : α} :
    Reach R x y → Reach R y z → Reach R x z := reach_trans R
theorem star_97_341 (R : Rel α) {x y z : α} :
    Reach R y x → Reach R z y → Reach R z x := fun h₁ h₂ => reach_trans R h₂ h₁

theorem star_97_35 (R : Rel α) (s : Set α) (hs : closed R s) {x y : α} :
    s x → Reach R x y → s y := by
  intro hx h
  induction h with
  | refl => exact hx
  | tail _ hr ih => exact hs ih hr

theorem star_97_36 (R : Rel α) {x y : α} (h : R x y) : Reach R x y :=
  .tail (.refl x) h
theorem star_97_37 (R : Rel α) {x y : α} (h : Reach R x y) : sameFamily R x y := Or.inl h
theorem star_97_38 (R : Rel α) {x y : α} (h : Reach R y x) : sameFamily R x y := Or.inr h

theorem star_97_4 (R : Rel α) {x y : α} (hx : root R x) (h : Reach R y x) : y = x := by
  cases h with
  | refl => rfl
  | tail _ hr => exact False.elim (hx ⟨_, hr⟩)

theorem star_97_401 (R : Rel α) (s : Set α) (hs : closed R s) {x y : α}
    (hx : s x) (h : Reach R x y) : s y := star_97_35 R s hs hx h

theorem star_97_402 (R : Rel α) {x y : α} (hx : root R x)
    (h : Reach R y x) : y = x := star_97_4 R hx h

theorem star_97_403 (R : Rel α) {x y z : α}
    (hxy : Reach R x y) (hyz : Reach R y z) : Reach R x z := reach_trans R hxy hyz

theorem star_97_41 (R : Rel α) {x y : α} (h : Reach R x y) : sameFamily R x y := Or.inl h
theorem star_97_42 (R : Rel α) {x y : α} (h : sameFamily R x y) : sameFamily R y x :=
  (star_97_242 (R := R) (x := x) (y := y)).mp h

theorem star_97_43 (R : Rel α) (hf : functionalRel R) {x y z : α}
    (hxy : R x y) (hxz : R x z) : y = z := hf hxy hxz

end PM.Architecture.Star97NextKernel
