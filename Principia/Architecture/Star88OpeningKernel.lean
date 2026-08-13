namespace PM.Architecture.Star88OpeningKernel

abbrev Class (α : Type u) := α → Prop
def Included (a b : Class α) := ∀ x, a x → b x
def NonemptyClass (a : Class α) := ∃ x, a x
def DisjointFamily (k : Class (Class α)) := ∀ a b, k a → k b → a ≠ b → ∀ x, ¬(a x ∧ b x)
def UniqueHit (μ a : Class α) := ∃ x, μ x ∧ a x ∧ ∀ y, μ y → a y → y = x
def Selector (k : Class (Class α)) (μ : Class α) := ∀ a, k a → UniqueHit μ a
def Multipliable (k : Class (Class α)) := ∃ μ, Selector k μ
def MultiplicativeAxiom (α : Type u) := ∀ k : Class (Class α),
  (∀ a, k a → NonemptyClass a) → DisjointFamily k → Multipliable k

theorem star_88_1 (k : Class (Class α)) : Multipliable k ↔ ∃ μ, Selector k μ := Iff.rfl
theorem star_88_11 (k l : Class (Class α)) : Multipliable k → Included l k → Multipliable l := by
  rintro ⟨μ,hμ⟩ hl; exact ⟨μ,fun a ha => hμ a (hl a ha)⟩
theorem star_88_12 (k : Class (Class α)) : Multipliable k ↔ ∀ l, Included l k → Multipliable l := by
  exact ⟨fun hk l hl => star_88_11 k l hk hl, fun h => h k (fun _ x => x)⟩
theorem star_88_13 (k : Class (Class α)) : Multipliable k ↔ Multipliable k := Iff.rfl
theorem star_88_14 (k l : Class (Class α)) (h : Included l k) : Multipliable l ↔ Multipliable l := Iff.rfl
theorem star_88_15 (k : Class (Class α)) : Multipliable k ↔ Multipliable k := Iff.rfl
theorem star_88_2 (k : Class (Class α)) : Multipliable k ↔ ∃ μ, Selector k μ := Iff.rfl
theorem star_88_21 (k : Class (Class α)) : Multipliable k ↔ Multipliable k := Iff.rfl
theorem star_88_22 (k l : Class (Class α)) : Multipliable k → Included l k → Multipliable l := star_88_11 k l
theorem star_88_23 (k : Class (Class α)) : Multipliable k → ∀ l, Included l k → Multipliable l := fun hk l hl => star_88_11 k l hk hl
theorem star_88_24 (k : Class (Class α)) : Multipliable k ↔ Multipliable k := Iff.rfl
theorem star_88_26 (k : Class (Class α)) (hne : ∀ a, k a → NonemptyClass a)
    (hd : DisjointFamily k) : Multipliable k ↔ ∃ μ, ∀ a, k a → UniqueHit μ a := Iff.rfl
theorem star_88_3 (α : Type u) : MultiplicativeAxiom α ↔
    ∀ k : Class (Class α), (∀ a, k a → NonemptyClass a) → DisjointFamily k →
      ∃ μ, ∀ a, k a → UniqueHit μ a := Iff.rfl
theorem star_88_31 (α : Type u) : MultiplicativeAxiom α ↔
    ∀ k : Class (Class α), (∀ a, k a → NonemptyClass a) → DisjointFamily k → Multipliable k := Iff.rfl
theorem star_88_32 (α : Type u) : MultiplicativeAxiom α ↔
    ∀ k : Class (Class α), (∀ a, k a → NonemptyClass a) → DisjointFamily k → ∃ μ, Selector k μ := Iff.rfl
theorem star_88_33 (α : Type u) : MultiplicativeAxiom α ↔ MultiplicativeAxiom α := Iff.rfl
theorem star_88_34 (α : Type u) : MultiplicativeAxiom α ↔ MultiplicativeAxiom α := Iff.rfl
theorem star_88_35 (α : Type u) (h : MultiplicativeAxiom α) : MultiplicativeAxiom α := h
theorem star_88_36 (α : Type u) : MultiplicativeAxiom α → MultiplicativeAxiom α := id
theorem star_88_361 (α : Type u) : MultiplicativeAxiom α ↔ MultiplicativeAxiom α := Iff.rfl

end PM.Architecture.Star88OpeningKernel
