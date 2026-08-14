/-! Extensional simple-type kernel for PM I ✱97, first macro-lot. -/
namespace PM.Architecture.Star97Kernel

abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def field (R : Rel α) : Set α := fun x => (∃ y, R x y) ∨ ∃ y, R y x
def forward (R : Rel α) (x : α) : Set α := fun y => R y x
def backward (R : Rel α) (x : α) : Set α := fun y => R x y
def family (R : Rel α) (x : α) : Set α :=
  fun y => R y x ∨ (y = x ∧ field R x) ∨ R x y
def symmetric (R : Rel α) : Rel α := fun x y => R x y ∨ R y x
def connected (R : Rel α) (x y : α) : Prop := family R x y
def linearOnField (R : Rel α) : Prop :=
  ∀ ⦃x y⦄, field R x → field R y → x = y ∨ R x y ∨ R y x

def star_97_01 (R : Rel α) (x y : α) : Prop :=
  R y x ∨ (y = x ∧ field R x) ∨ R x y

theorem star_97_1 (R : Rel α) (x y : α) :
    family R x y ↔ R y x ∨ (y = x ∧ field R x) ∨ R x y := Iff.rfl

theorem star_97_101 (R : Rel α) (x y : α) :
    family R x y ↔ family R y x := by
  constructor <;> rintro (h | ⟨rfl, h⟩ | h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inl h

theorem star_97_11 (R : Rel α) {x y : α} (h : family R x y) : field R y := by
  rcases h with h | ⟨rfl, h⟩ | h
  · exact Or.inl ⟨x, h⟩
  · exact h
  · exact Or.inr ⟨x, h⟩

theorem star_97_111 (R : Rel α) (x : α) : field R x ↔ family R x x := by
  constructor
  · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact star_97_11 R

theorem star_97_12 (R : Rel α) {x : α} (hx : field R x) : ∃ y, family R x y :=
  ⟨x, (star_97_111 R x).mp hx⟩

theorem star_97_13 (R : Rel α) (x y : α) :
    family (symmetric R) x y ↔ family (symmetric R) y x :=
  star_97_101 (symmetric R) x y

theorem star_97_14 (R : Rel α) {x y : α} (h : R x y) :
    family R x y ∧ family R y x := ⟨Or.inr (Or.inr h), Or.inl h⟩

theorem star_97_15 (R : Rel α) {x y : α} (h : family R x y) :
    field R x ∧ field R y := by
  exact ⟨star_97_11 R ((star_97_101 R x y).mp h), star_97_11 R h⟩

theorem star_97_16 (R : Rel α) {x y : α} (h : family R x y) :
    family R y x := (star_97_101 R x y).mp h

theorem star_97_17 (R : Rel α) (x y : α) :
    connected R x y ↔ family R x y := Iff.rfl

theorem star_97_18 (R : Rel α) {x y : α} (h : family R x y) :
    field R x ∧ field R y := star_97_15 R h

theorem star_97_2 (R : Rel α) {x y : α} (h : R x y) : family R x y :=
  Or.inr (Or.inr h)

theorem star_97_21 (R : Rel α) {x y : α} (h : R y x) : family R x y := Or.inl h

theorem star_97_22 (R : Rel α) {x : α} (h : field R x) : family R x x :=
  (star_97_111 R x).mp h

theorem star_97_23 (R : Rel α) :
    (∀ x y, field R x → field R y → family R x y) ↔ linearOnField R := by
  constructor
  · intro h x y hx hy
    rcases h x y hx hy with h | ⟨h, _⟩ | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
  · intro h x y hx hy
    rcases h hx hy with h | h | h
    · subst y; exact (star_97_111 R x).mp hx
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

theorem star_97_231 (R : Rel α) (h : linearOnField R) {x : α} (hx : field R x) :
    ∀ ⦃y⦄, field R y → family R x y :=
  fun {_} hy => (star_97_23 R).mpr h x _ hx hy

theorem star_97_24 (R : Rel α) (x y : α) :
    family R x y → family R y x := star_97_16 R

end PM.Architecture.Star97Kernel
