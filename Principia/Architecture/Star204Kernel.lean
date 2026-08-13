/-! Strict-linear-order kernel for PM II ✱204. -/
namespace PM.Architecture.Star204Kernel
abbrev Rel (α : Type u) := α → α → Prop
def converse (R : Rel α) : Rel α := fun x y => R y x
def empty : Rel α := fun _ _ => False
def Transitive (R : Rel α) := ∀ ⦃x y z⦄, R x y → R y z → R x z
def Irreflexive (R : Rel α) := ∀ x, ¬R x x
def Connex (R : Rel α) := ∀ ⦃x y⦄, x ≠ y → R x y ∨ R y x
structure Serial (R : Rel α) : Prop where
 trans : Transitive R
 irrefl : Irreflexive R
 connex : Connex R

theorem star_204_01 (R : Rel α) : Serial R ↔ Transitive R ∧ Irreflexive R ∧ Connex R :=
 ⟨fun h => ⟨h.trans,h.irrefl,h.connex⟩, fun h => ⟨h.1,h.2.1,h.2.2⟩⟩
theorem star_204_1 (R : Rel α) (h : Serial R) : Transitive R ∧ Irreflexive R ∧ Connex R := ⟨h.trans,h.irrefl,h.connex⟩
theorem star_204_11 (R : Rel α) (h : Serial R) {x y : α} : x ≠ y → R x y ∨ R y x := fun hn => h.connex hn
theorem star_204_12 (R : Rel α) (h : Serial R) {x y : α} : R x y → ¬R y x := by
 intro hxy hyx; exact h.irrefl x (h.trans hxy hyx)
theorem star_204_121 (R : Rel α) (h : Serial R) {x y : α} : R x y → x ≠ y := by
 intro hxy e; subst y; exact h.irrefl x hxy
theorem star_204_13 (R : Rel α) (h : Serial R) : ∀ x, ¬R x x := h.irrefl
theorem star_204_14 (R : Rel α) (h : Serial R) {x y z : α} : R x y → R y z → R x z := fun hxy hyz => h.trans hxy hyz
theorem star_204_15 (R : Rel α) (h : Serial R) {x y z : α} : R x y → R y z → x ≠ z := by
 intro hxy hyz e; subst z; exact h.irrefl x (h.trans hxy hyz)
theorem star_204_151 (R : Rel α) (h : Serial R) {x y : α} : R x y → ¬R y x := star_204_12 R h
theorem star_204_16 (R : Rel α) : Serial R ↔ Connex R ∧ Transitive R ∧ Irreflexive R :=
 ⟨fun h => ⟨h.connex,h.trans,h.irrefl⟩, fun h => ⟨h.2.1,h.2.2,h.1⟩⟩
theorem star_204_2 (R : Rel α) : Serial R ↔ Serial (converse R) := by
 constructor
 · intro h; exact ⟨(fun {_ _ _} hxy hyz => h.trans hyz hxy), h.irrefl, (fun {_ _} hn => (h.connex hn).elim Or.inr Or.inl)⟩
 · intro h; exact ⟨(fun {_ _ _} hxy hyz => h.trans hyz hxy), h.irrefl, (fun {_ _} hn => (h.connex hn).elim Or.inr Or.inl)⟩
theorem star_204_21 (R : Rel α) (h : Serial R) : Serial (converse R) := (star_204_2 R).mp h
theorem star_204_22 (R : Rel α) : converse (converse R) = R := rfl
theorem star_204_23 (R : Rel α) (h : Serial (converse R)) : Serial R := (star_204_2 R).mpr h
theorem star_204_24 : Serial (empty : Rel PEmpty) :=
  ⟨(fun {_ _ _} h => False.elim h), (fun x => PEmpty.elim x),
    (fun {x} => PEmpty.elim x)⟩
theorem star_204_25 : Serial (fun a b : Bool => a = false ∧ b = true) := by
 refine ⟨?_,?_,?_⟩
 · rintro a b c ⟨_,rfl⟩ ⟨h,_⟩
   contradiction
 · intro a
   cases a <;> simp
 · intro a b hn
   cases a <;> cases b <;> simp_all
theorem star_204_26 (R : Rel α) (h : Serial R) {x y : α} (hxy : R x y) : x ≠ y := star_204_121 R h hxy
theorem star_204_27 (R : Rel α) (h : Serial R) {x y : α} (hn : x ≠ y) : R x y ∨ R y x := h.connex hn
end PM.Architecture.Star204Kernel
