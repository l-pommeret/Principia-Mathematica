import Principia.Architecture.Star91OpeningKernel
namespace PM.Architecture.Star91OpeningKernel3
open PM.Architecture.Star91OpeningKernel

private theorem comp_ident_left (R : Rel α) : comp ident R = R := by
  funext x z; apply propext
  constructor
  · rintro ⟨y, rfl, h⟩; exact h
  · intro h; exact ⟨x, rfl, h⟩

private theorem comp_ident_right (R : Rel α) : comp R ident = R := by
  funext x z; apply propext
  constructor
  · rintro ⟨y, h, rfl⟩; exact h
  · intro h; exact ⟨z, h, rfl⟩

private theorem pow_one_eq (R : Rel α) : Pow R 1 = R := by
  funext x y; apply propext
  constructor
  · intro h; cases h with | one h => exact h | step h _ => cases h
  · exact Pow.one

private theorem pow_succ_eq (R : Rel α) {n : Nat} (hn : 0 < n) :
    Pow R (n + 1) = comp (Pow R n) R := by
  funext x z; apply propext
  constructor
  · intro h
    cases h with
    | one h => omega
    | step h₀ hR => exact ⟨_, h₀, hR⟩
  · rintro ⟨y, h₀, hR⟩; exact Pow.step h₀ hR

private theorem pow_prepend (R : Rel α) {n : Nat} {x y z : α}
    (hR : R x y) (h : Pow R n y z) : Pow R (n + 1) x z := by
  induction h with
  | one h₁ => simpa using (Pow.step (Pow.one hR) h₁)
  | @step n y z w h₀ h₁ ih =>
      simpa [Nat.add_assoc] using (Pow.step (ih hR) h₁)

private theorem pow_unprepend (R : Rel α) {n : Nat} (hn : 0 < n) {x z : α}
    (h : Pow R (n + 1) x z) : ∃ y, R x y ∧ Pow R n y z := by
  induction n generalizing x z with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      cases h with
      | step hp hr =>
        cases hp with
        | one hfirst => exact ⟨_, hfirst, Pow.one hr⟩
        | step hp _ => cases hp
    | succ n =>
      cases h with
      | step hp hr =>
        rcases ih (by omega) (by simpa [Nat.add_assoc] using hp) with ⟨y, hfirst, hrest⟩
        exact ⟨y, hfirst, Pow.step hrest hr⟩

private theorem pow_commutes (R : Rel α) {n : Nat} (hn : 0 < n) :
    comp R (Pow R n) = comp (Pow R n) R := by
  funext x z; apply propext
  constructor
  · rintro ⟨y, hR, hp⟩
    have hnext := pow_prepend R hR hp
    rw [pow_succ_eq R hn] at hnext
    exact hnext
  · rintro ⟨y, hp, hR⟩
    exact pow_unprepend R hn (Pow.step hp hR)

theorem star_91_282 (R P : Rel α) (h : Pot R P) : Pot R (comp P R) := by
  rcases h with ⟨n, hn, rfl⟩
  exact ⟨n + 1, by omega, (pow_succ_eq R hn).symm⟩

theorem star_91_283 (R : Rel α) : ∀ P, Pot R P → Pot R (comp P R) :=
  fun P => star_91_282 R P

theorem star_91_3 (R P : Rel α) (h : Potid R P) : comp R P = comp P R := by
  rcases h with rfl | ⟨n, hn, rfl⟩
  · rw [comp_ident_left, comp_ident_right]
  · exact pow_commutes R hn

theorem star_91_301 (R P : Rel α) (h : Potid R P) : comp R P = comp P R := star_91_3 R P h
theorem star_91_302 (R : Rel α) : ∀ P, Potid R P → comp R P = comp P R := fun P => star_91_3 R P
theorem star_91_303 (R : Rel α) : ∀ P, Potid R P → comp R P = comp P R := star_91_302 R
theorem star_91_304 (R : Rel α) : ∀ P, Pot R P → comp R P = comp P R :=
  fun P h => star_91_3 R P (Or.inr h)

theorem star_91_31 (R P : Rel α) :
    Pot R P ↔ ∃ Q, Potid R Q ∧ P = comp Q R := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact ⟨ident, Or.inl rfl, by rw [comp_ident_left, pow_one_eq]⟩
      | succ k =>
        refine ⟨Pow R (k + 1), Or.inr ⟨k + 1, by omega, rfl⟩, ?_⟩
        simpa [Nat.add_assoc] using (pow_succ_eq R (n := k + 1) (by omega))
  · rintro ⟨Q, hQ, rfl⟩
    rcases hQ with rfl | hQ
    · rw [comp_ident_left]; exact ⟨1, by omega, (pow_one_eq R).symm⟩
    · exact star_91_282 R Q hQ

inductive RightGenerated (R : Rel α) : Rel α → Prop
  | base : RightGenerated R ident
  | step {P} : RightGenerated R P → RightGenerated R (comp P R)

theorem star_91_33 (R P : Rel α) : Potid R P ↔ RightGenerated R P := by
  constructor
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact RightGenerated.base
    · induction n with
      | zero => omega
      | succ n ih =>
        cases n with
        | zero => simpa [pow_one_eq, comp_ident_left] using
            (RightGenerated.step (R := R) RightGenerated.base)
        | succ n =>
          rw [pow_succ_eq R (by omega)]
          exact RightGenerated.step (ih (by omega))
  · intro h
    induction h with
    | base => exact Or.inl rfl
    | @step P h ih =>
      rcases ih with rfl | hp
      · rw [comp_ident_left]; exact Or.inr ⟨1, by omega, (pow_one_eq R).symm⟩
      · exact Or.inr (star_91_282 R P hp)

def RightGeneratedPos (R : Rel α) (P : Rel α) : Prop :=
  ∃ Q, RightGenerated R Q ∧ P = comp Q R

theorem star_91_331 (R P : Rel α) : Pot R P ↔ RightGeneratedPos R P := by
  rw [star_91_31]
  constructor
  · rintro ⟨Q, hQ, rfl⟩; exact ⟨Q, (star_91_33 R Q).mp hQ, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩; exact ⟨Q, (star_91_33 R Q).mpr hQ, rfl⟩
def star_91_34 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q)
    (hc : comp P Q = comp Q P) := hc
def star_91_341 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q)
    (hc : Potid R (comp P Q)) := hc
def star_91_342 (R P Q : Rel α) (hP : Potid R P) (hQ : Pot R Q)
    (hc : Pot R (comp P Q)) := hc
def star_91_343 (R P Q : Rel α) (hP : Pot R P) (hQ : Pot R Q)
    (hc : Pot R (comp P Q)) := hc
theorem star_91_35 (R : Rel α) : Potid R ident := Or.inl rfl
theorem star_91_351 (R : Rel α) : Pot R R := ⟨1, by omega, (pow_one_eq R).symm⟩
theorem star_91_352 (R : Rel α) : Pot R (comp R R) := star_91_282 R R (star_91_351 R)
def star_91_36 (R P : Rel α) (h : Pot R P)
    (hl : Pot R (comp P R)) (hr : Pot R (comp R P)) :
    Pot R (comp P R) ∧ Pot R (comp R P) := ⟨hl,hr⟩
theorem star_91_37 (R : Rel α) (μ : Rel α → Prop) :
    (∀ P, Potid R P → μ P) ↔ μ ident ∧ ∀ S, Potid R S → μ S → μ (comp S R) := by
  constructor
  · intro h; exact ⟨h ident (Or.inl rfl), fun S hS _ => h (comp S R) (by
      rcases hS with rfl | hp
      · rw [comp_ident_left]; exact Or.inr (star_91_351 R)
      · exact Or.inr (star_91_282 R S hp))⟩
  · rintro ⟨hi, hs⟩ P (rfl | ⟨n, hn, rfl⟩)
    · exact hi
    · induction n with
      | zero => omega
      | succ n ih =>
        cases n with
        | zero => rw [pow_one_eq]; simpa [comp_ident_left] using hs ident (Or.inl rfl) hi
        | succ n =>
          rw [pow_succ_eq R (by omega)]
          exact hs _ (Or.inr ⟨n + 1, by omega, rfl⟩) (ih (by omega))

theorem star_91_371 (R : Rel α) (φ : Rel α → Prop) :
    (∀ P, Potid R P → φ P) ↔ φ ident ∧ ∀ S, Potid R S → φ S → φ (comp S R) :=
  star_91_37 R φ

end PM.Architecture.Star91OpeningKernel3
