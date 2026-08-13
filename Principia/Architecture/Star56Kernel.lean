/-!
# PM I ✱56 — the relational number two

Source: *Principia Mathematica*, first edition, volume I, ✱56 (pp. 396–402),
Project Gutenberg ebook 78050.  This module isolates the extensional kernel:
`x ↓ y` is the relation containing exactly `(x,y)`; ✱56·01 defines the
cardinal of such relations and ✱56·02 its diverse-member restriction.
-/

namespace PM.Architecture.Star56Kernel

abbrev Rel (α : Type u) := α → α → Prop

def couple (x y : α) : Rel α := fun a b => a = x ∧ b = y
def empty : Rel α := fun _ _ => False
def inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y
def subrel (R S : Rel α) : Prop := ∀ x y, R x y → S x y
def nonemptyRel (R : Rel α) : Prop := ∃ x y, R x y

/-- ✱56·01. -/
def dotTwo (R : Rel α) : Prop := ∃ x y, R = couple x y
/-- ✱56·02. -/
def twoR (R : Rel α) : Prop := ∃ x y, x ≠ y ∧ R = couple x y
/-- ✱56·03. -/
def zeroR (R : Rel α) : Prop := R = empty

theorem star_56_1 (R : Rel α) : dotTwo R ↔ ∃ x y, R = couple x y := Iff.rfl
theorem star_56_104 (R : Rel α) : zeroR R ↔ R = empty := Iff.rfl
theorem star_56_11 (R : Rel α) :
    twoR R ↔ ∃ x y, x ≠ y ∧ R = couple x y := Iff.rfl

theorem star_56_103 (R : Rel α) : dotTwo R → nonemptyRel R := by
  rintro ⟨x, y, rfl⟩
  exact ⟨x, y, rfl, rfl⟩

theorem star_56_12 (R : Rel α) :
    twoR R ↔ dotTwo R ∧ subrel R (fun x y => x ≠ y) := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨⟨x, y, rfl⟩, ?_⟩
    rintro a b ⟨rfl, rfl⟩
    exact hxy
  · rintro ⟨⟨x, y, rfl⟩, h⟩
    exact ⟨x, y, h x y ⟨rfl, rfl⟩, rfl⟩

theorem star_56_121 (R : Rel α) : twoR R → dotTwo R := by
  rintro ⟨x, y, _, h⟩
  exact ⟨x, y, h⟩

theorem star_56_122 (R : Rel α) : twoR R → nonemptyRel R := by
  intro h
  exact star_56_103 R (star_56_121 R h)

theorem star_56_13 (R : Rel α) :
    dotTwo R ∧ ¬ twoR R ↔ ∃ a, R = couple a a := by
  constructor
  · rintro ⟨⟨x, y, hR⟩, hn⟩
    by_cases hxy : x = y
    · subst y
      exact ⟨x, hR⟩
    · exact False.elim (hn ⟨x, y, hxy, hR⟩)
  · rintro ⟨a, rfl⟩
    refine ⟨⟨a, a, rfl⟩, ?_⟩
    rintro ⟨x, y, hxy, h⟩
    have hm : couple a a x y := by
      rw [h]
      exact ⟨rfl, rfl⟩
    exact hxy (hm.1.trans hm.2.symm)

theorem star_56_16 (x y : α) : dotTwo (couple x y) := ⟨x, y, rfl⟩

theorem star_56_17 (x y : α) :
    (twoR (couple x y) ↔ x ≠ y) ∧
      (twoR (couple y x) ↔ x ≠ y) := by
  constructor
  · constructor
    · rintro ⟨a, b, hab, h⟩ hxy
      subst y
      have hm : couple x x a b := by rw [h]; exact ⟨rfl, rfl⟩
      exact hab (hm.1.trans hm.2.symm)
    · intro h
      exact ⟨x, y, h, rfl⟩
  · constructor
    · rintro ⟨a, b, hab, h⟩ hxy
      subst y
      have hm : couple x x a b := by rw [h]; exact ⟨rfl, rfl⟩
      exact hab (hm.1.trans hm.2.symm)
    · intro h
      exact ⟨y, x, fun e => h e.symm, rfl⟩

theorem star_56_2 (R : Rel α) :
    dotTwo R ↔ ∃ x y, ∀ z w, R z w ↔ z = x ∧ w = y := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, y, fun _ _ => Iff.rfl⟩
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    funext z w
    exact propext (h z w)

theorem star_56_21 (R : Rel α) :
    dotTwo R ↔ nonemptyRel R ∧
      ∀ x y z w, R x y → R z w → x = z ∧ y = w := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨⟨a, b, rfl, rfl⟩, ?_⟩
    rintro x y z w ⟨hx, hy⟩ ⟨hz, hw⟩
    exact ⟨hx.trans hz.symm, hy.trans hw.symm⟩
  · rintro ⟨⟨x, y, hxy⟩, hu⟩
    refine ⟨x, y, ?_⟩
    funext z w
    apply propext
    constructor
    · intro h
      exact hu z w x y h hxy
    · rintro ⟨rfl, rfl⟩
      exact hxy

theorem star_56_22 : ¬ dotTwo (empty : Rel α) := by
  rintro ⟨x, y, h⟩
  have hm : empty x y := by
    rw [h]
    exact ⟨rfl, rfl⟩
  exact hm

theorem star_56_261 (R S : Rel α) :
    dotTwo R → subrel S R → (S = empty ∨ S = R) := by
  rintro ⟨x, y, rfl⟩ hs
  by_cases hxy : S x y
  · right
    funext a b
    apply propext
    constructor
    · exact hs a b
    · rintro ⟨rfl, rfl⟩
      exact hxy
  · left
    funext a b
    apply propext
    constructor
    · intro hab
      have hc := hs a b hab
      exact hxy (hc.1 ▸ hc.2 ▸ hab)
    · exact False.elim

theorem star_56_262 (R S : Rel α) (hR : dotTwo R) (hS : subrel S R) :
    nonemptyRel S ↔ S = R := by
  constructor
  · intro hn
    rcases star_56_261 R S hR hS with he | he
    · subst S
      obtain ⟨x, y, h⟩ := hn
      exact False.elim h
    · exact he
  · intro he
    subst S
    exact star_56_103 R hR

theorem star_56_27 (R S : Rel α) (hR : dotTwo R) :
    nonemptyRel (inter R S) ↔ dotTwo (inter R S) := by
  constructor
  · intro hn
    have hs : subrel (inter R S) R := fun _ _ h => h.1
    have he := (star_56_262 R (inter R S) hR hs).mp hn
    rw [he]
    exact hR
  · exact star_56_103 (inter R S)

theorem star_56_32 (P Q : Rel α) (hP : dotTwo P) :
    dotTwo (inter P Q) ∨ inter P Q = empty := by
  by_cases hn : nonemptyRel (inter P Q)
  · exact Or.inl ((star_56_27 P Q hP).mp hn)
  · right
    funext x y
    apply propext
    exact ⟨fun h => hn ⟨x, y, h⟩, False.elim⟩

end PM.Architecture.Star56Kernel
