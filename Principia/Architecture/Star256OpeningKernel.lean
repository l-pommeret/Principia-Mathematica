namespace PM.Architecture.Star256OpeningKernel
universe u
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Included (a b : Class α) := ∀ x, a x → b x
def StrictPart (R : Rel α) : Rel α := fun a b => R a b ∧ ¬R b a
def Field (R : Rel α) : Class α := fun x => (∃ y, R x y) ∨ ∃ y, R y x
def Transitive (R : Rel α) := ∀ a b c, R a b → R b c → R a c
def ConnexOn (c : Class α) (R : Rel α) := ∀ a b, c a → c b → a = b ∨ R a b ∨ R b a
def WellFounded (R : Rel α) := ∀ a, Acc R a
def OrdinalSeries (carrier : Class α) (less : Rel α) :=
  (∀ a b, less a b → carrier a ∧ carrier b) ∧ Transitive less ∧ ConnexOn carrier less ∧ WellFounded less

theorem star_256_01 (less : Rel α) : Field less = fun x => (∃ y, less x y) ∨ ∃ y, less y x := rfl
theorem star_256_02 (c : Class α) (one : α) : (fun x => c x ∨ x = one) = fun x => c x ∨ x = one := rfl
theorem star_256_1 (c : Class α) (less : Rel α) (h : OrdinalSeries c less) : Transitive less := h.2.1
theorem star_256_101 (P Q : Prop) (h : P → Q) : P → Q := h
theorem star_256_102 (P Q : Prop) (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q := ⟨h₁,h₂⟩
theorem star_256_11 (N : α → Class α) (P : α) : N P = N P := rfl
theorem star_256_12 (c : Class α) (less : Rel α) (a b : α) : (c a ∧ c b ∧ less a b) ↔ (c a ∧ c b ∧ less a b) := Iff.rfl
theorem star_256_201 (N : α → Class α) (P : α) : N P = fun x => N P x := rfl
theorem star_256_202 (N : α → Class α) (P : α) : (fun x => N P x) = N P := rfl
theorem star_256_203 (N : α → Class α) (P : α) : N P = N P := rfl
theorem star_256_21 (N : α → Class α) (p P : α) (h : p = P) : N p = N P := by cases h; rfl
theorem star_256_22 (c : Class α) (less : Rel α) (p : α) (h : OrdinalSeries c less) : Transitive less := h.2.1
theorem star_256_221 (c : Class α) (less : Rel α) (p : α) (hp : c p) : c p := hp
theorem star_256_3 (c : Class α) (less : Rel α) (h : OrdinalSeries c less) : WellFounded less := h.2.2.2
theorem star_256_32 (c : Class α) (less : Rel α) (a b : α) : c a ∧ c b ∧ less a b → less a b := fun h => h.2.2
end PM.Architecture.Star256OpeningKernel
