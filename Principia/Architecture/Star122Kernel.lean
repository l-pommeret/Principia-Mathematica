/-! Order-theoretic kernel for PM II ✱122 progressions. -/
namespace PM.Architecture.Star122Kernel
abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
inductive Reach (R : Rel α) : α → α → Prop
 | refl x : Reach R x x
 | tail {x y z} : Reach R x y → R y z → Reach R x z
def domain (R : Rel α) : Set α := fun x => ∃ y, R x y
def range (R : Rel α) : Set α := fun y => ∃ x, R x y
def field (R : Rel α) : Set α := fun x => domain R x ∨ range R x
def subset (s t : Set α) : Prop := ∀ ⦃x⦄, s x → t x
def Functional (R : Rel α) := ∀ ⦃x y z⦄, R x y → R x z → y = z
def Injective (R : Rel α) := ∀ ⦃x y z⦄, R x z → R y z → x = y
def Linear (R : Rel α) := ∀ ⦃x y⦄, field R x → field R y → Reach R x y ∨ Reach R y x
structure Progression (R : Rel α) : Prop where
 functional : Functional R
 injective : Injective R
 linear : Linear R
 range_domain : subset (range R) (domain R)
 acyclic : ∀ ⦃x y⦄, R x y → ¬R y x

theorem star_122_01 (R : Rel α) : Progression R ↔
    Functional R ∧ Injective R ∧ Linear R ∧ subset (range R) (domain R) ∧
      (∀ ⦃x y⦄, R x y → ¬R y x) := by
  exact ⟨fun h => ⟨h.functional,h.injective,h.linear,h.range_domain,h.acyclic⟩,
    fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩⟩
theorem star_122_1 (R : Rel α) (h : Progression R) : Functional R ∧ Injective R := ⟨h.functional,h.injective⟩
theorem star_122_11 (R : Rel α) (h : Progression R) : Linear R := h.linear
theorem star_122_12 (R : Rel α) : Progression R → Linear R := fun h => h.linear
theorem star_122_14 (R : Rel α) (h : Progression R) : subset (range R) (domain R) := h.range_domain
theorem star_122_141 (R : Rel α) (h : Progression R) : field R = domain R := by
  funext x; apply propext
  exact ⟨fun hx => hx.elim id (fun hr => h.range_domain hr), Or.inl⟩
theorem star_122_142 (R : Rel α) (h : Progression R) {x : α} : field R x → domain R x := by rw [star_122_141 R h]; exact id
theorem star_122_143 (R : Rel α) (h : Progression R) : subset (range R) (field R) :=
  fun {_} hx => Or.inr hx
theorem star_122_15 (R : Rel α) (h : Progression R) {x y : α} : R x y → field R x ∧ field R y := by
  intro hr; exact ⟨Or.inl ⟨y,hr⟩,Or.inr ⟨x,hr⟩⟩
theorem star_122_151 (R : Rel α) (x : α) : Reach R x x := .refl x
theorem star_122_152 (R : Rel α) {x y : α} (h : R x y) : Reach R x y := .tail (.refl x) h
theorem star_122_16 (R : Rel α) (h : Progression R) {x y : α} (hxy : R x y) : x ≠ y → ¬R y x := by
  intro _; exact h.acyclic hxy
theorem star_122_17 (R : Rel α) (h : Progression R) : Functional R ∧ Linear R := ⟨h.functional,h.linear⟩
theorem star_122_2 (R : Rel α) (h : Progression R) {x y : α}
    (hx : field R x) (hy : field R y) : Reach R x y ∨ Reach R y x := h.linear hx hy
theorem star_122_21 (R : Rel α) (h : Progression R) {x y : α}
    (hx : field R x) (hy : field R y) : Reach R x y ∨ x = y ∨ Reach R y x := by
  exact (h.linear hx hy).elim Or.inl (fun q => Or.inr (Or.inr q))
theorem star_122_22 (R : Rel α) (h : Progression R) (s : Set α) (hs : subset s (field R))
    {x y : α} (hx : s x) (hy : s y) : Reach R x y ∨ Reach R y x := h.linear (hs hx) (hs hy)
theorem star_122_23 (R : Rel α) (h : Progression R) {x y : α}
    (hx : field R x) (hy : field R y) : Reach R x y ∨ x = y ∨ Reach R y x := star_122_21 R h hx hy
theorem star_122_231 (R : Rel α) (h : Progression R) (s : Set α)
    (hs : ∀ x, ¬s x) : (∀ x, ¬s x) := hs
end PM.Architecture.Star122Kernel
