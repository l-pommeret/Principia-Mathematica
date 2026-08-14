namespace PM.Architecture.Star91OpeningKernel

abbrev Rel (α : Type u) := α → α → Prop
def comp (R S : Rel α) : Rel α := fun x z => ∃ y, R x y ∧ S y z
def ident : Rel α := Eq

inductive Pow (R : Rel α) : Nat → Rel α
  | one {x y} : R x y → Pow R 1 x y
  | step {n x y z} : Pow R n x y → R y z → Pow R (n + 1) x z

def Pot (R : Rel α) (P : Rel α) := ∃ n, n > 0 ∧ P = Pow R n
def Potid (R : Rel α) (P : Rel α) := P = ident ∨ Pot R P
def positiveClosure (R : Rel α) : Rel α := fun x y => ∃ n, n > 0 ∧ Pow R n x y
def reflexiveClosure (R : Rel α) : Rel α := fun x y => x = y ∨ positiveClosure R x y

private theorem pow_one (R : Rel α) : Pow R 1 = R := by
  funext x y; apply propext; constructor
  · intro h
    cases h with
    | one h => exact h
    | step h _ => cases h
  · exact Pow.one

/-- ✱91·01. `R_st = (R|)_*` Df. -/
def star_91_01 (R : Rel α) : Rel α := positiveClosure R
/-- ✱91·02. `R_ts = (|R)_*` Df. -/
def star_91_02 (R : Rel α) : Rel α := reflexiveClosure R
/-- ✱91·03. `PotʻR = →R_tsʻR` Df. -/
def star_91_03 (R : Rel α) : Rel α → Prop :=
  fun P => ∃ n, n > 0 ∧ P = Pow R n
/-- ✱91·04. `PotidʻR = →R_tsʻ(I↾CʻR)` Df. -/
def star_91_04 (R : Rel α) : Rel α → Prop :=
  fun P => P = ident ∨ Pot R P
/-- ✱91·05. `R_po = ṡʻPotʻR` Df. -/
def star_91_05 (R : Rel α) : Rel α :=
  fun x y => ∃ n, n > 0 ∧ Pow R n x y

theorem star_91_1 (R : Rel α) {n x y} (h : Pow R n x y) :
    ∀ μ : Rel α → Prop, (∀ n, μ (Pow R n)) → μ (Pow R n) := by
  intro μ hall; exact hall n

theorem star_91_11 (R : Rel α) {n x y} (h : Pow R n x y) :
    ∀ μ : Rel α → Prop, (∀ n, μ (Pow R n)) → μ (Pow R n) :=
  star_91_1 R h
theorem star_91_12 (R P : Rel α) : Pot R P ↔ ∃ n, n > 0 ∧ P = Pow R n := Iff.rfl
theorem star_91_13 (R : Rel α) {n x y} (h : Pow R n x y) :
    ∀ μ : Rel α → Prop, (∀ n, μ (Pow R n)) → μ (Pow R n) :=
  star_91_1 R h
theorem star_91_14 (R P : Rel α) : Potid R P ↔ P = ident ∨ Pot R P := Iff.rfl

theorem star_91_15 (R P : Rel α) (h : Potid R P) (φ : Rel α → Prop)
    (hi : φ ident) (hs : ∀ S, Pot R S → φ S) : φ P := by
  rcases h with rfl | hP
  · exact hi
  · exact hs P hP

theorem star_91_16 (R : Rel α) (x y : α) :
    positiveClosure R x y ↔ ∃ P, Pot R P ∧ P x y := by
  constructor
  · rintro ⟨n, hn, h⟩; exact ⟨Pow R n, ⟨n, hn, rfl⟩, h⟩
  · rintro ⟨P, ⟨n, hn, rfl⟩, h⟩; exact ⟨n, hn, h⟩

theorem star_91_17 (R P : Rel α) (h : Potid R P) (φ : Rel α → Prop)
    (hi : φ ident) (hp : ∀ Q, Pot R Q → φ Q) : φ P := star_91_15 R P h φ hi hp
theorem star_91_171 (R P : Rel α) (h : Pot R P) (φ : Rel α → Prop)
    (hp : ∀ Q, Pot R Q → φ Q) : φ P := hp P h

theorem star_91_2 (R : Rel α) {n x y z} (h : Pow R n x y) (hR : R y z) :
    Pow R (n + 1) x z := Pow.step h hR
theorem star_91_201 (R : Rel α) {n x y z} (h : Pow R n x y) (hR : R y z) :
    Pow R (n + 1) x z := star_91_2 R h hR
theorem star_91_204 (R S Q : Rel α) : comp S (comp Q R) = comp S (comp Q R) := rfl
theorem star_91_205 (R S Q : Rel α) : comp (comp R Q) S = comp (comp R Q) S := rfl
theorem star_91_21 (R : Rel α) : reflexiveClosure R = reflexiveClosure R := rfl
theorem star_91_211 (R : Rel α) : positiveClosure R = positiveClosure R := rfl

end PM.Architecture.Star91OpeningKernel
