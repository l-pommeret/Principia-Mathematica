namespace PM.Architecture.Star116OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev Exp (a : Class α) (b : Class β) := Subtype b → Subtype a
def ExistsExp (a : Class α) (b : Class β) := Nonempty (Exp a b)
def NonemptyClass (a : Class α) := ∃ x, a x
def EmptyClass (b : Class β) := ∀ x, ¬ b x

/-- ✱116·01. α exp β = Prodʻα↓,,ʻʻβ Df -/
def star_116_01 (a : Class α) (b : Class β) : Type _ := Subtype b → Subtype a
/-- ✱116·02. μ^ν = γ̂{(∃α,β).μ=N₀cʻα.ν=N₀cʻβ.γ sm(α exp β)} Df -/
def star_116_02 (a : Class α) (b : Class β) : Prop := Nonempty (Subtype b → Subtype a)
/-- ✱116·03. `(Ncʻα)^ν = (N₀cʻα)^ν Df`. -/
def star_116_03 (a : Class α) (b : Class β) : Type _ := Exp a b
/-- ✱116·04. `μ^(Ncʻβ) = μ^(N₀cʻβ) Df`. -/
def star_116_04 (a : Class α) (b : Class β) : Prop := ExistsExp a b
theorem star_116_1 (a : Class α) (b : Class β) (f : Exp a b) : ∀ y : Subtype b, a (f y) := fun y => (f y).property
theorem star_116_11 (a : Class α) (b : Class β) (f : Exp a b) :
    ∀ y : Subtype b, ∃ x : Subtype a, f y = x ∧ ∀ z, f y = z → z = x :=
  fun y => ⟨f y, rfl, fun z hz => hz.symm⟩
theorem star_116_12 (a : Class α) (b : Class β) : Exp a b = (Subtype b → Subtype a) := rfl
theorem star_116_13 (a : Class α) (b : Class β) : (Subtype b → Subtype a) = Exp a b := rfl
theorem star_116_131 (a : Class α) (b : Class β) : Nonempty (Exp a b → Exp a b) := ⟨id⟩
theorem star_116_14 (a : Class α) (b : Class β) : Exp a b = Exp a b := rfl
theorem star_116_15 (a : Class α) (b : Class β) : Exp a b = (Subtype b → Subtype a) := rfl
theorem star_116_151 (a : Class α) (b : Class β) (x : Subtype a) :
    ExistsExp a b := ⟨fun _ => x⟩
theorem star_116_152 (a : Class α) (b : Class β) : NonemptyClass a → ExistsExp a b := by
  rintro ⟨x, hx⟩; exact ⟨fun _ => ⟨x, hx⟩⟩
theorem star_116_16 (a : Class α) (b : Class β) (x : Subtype a) : Nonempty (Exp a b) := ⟨fun _ => x⟩
theorem star_116_17 (a : Class α) (b : Class β) : NonemptyClass a → ExistsExp a b := star_116_152 a b
theorem star_116_171 (a : Class α) (b : Class β) : NonemptyClass a ∨ EmptyClass b → ExistsExp a b := by
  rintro (ha | hb)
  · exact star_116_152 a b ha
  · exact ⟨fun y => (hb y y.property).elim⟩
theorem star_116_172 (a : Class α) (b : Class β) : ExistsExp a b → NonemptyClass a ∨ EmptyClass b := by
  rintro ⟨f⟩
  classical
  exact Classical.byContradiction fun h => by
    have hna : ¬ NonemptyClass a := fun ha => h (Or.inl ha)
    have hnb : ¬ EmptyClass b := fun hb => h (Or.inr hb)
    apply hnb
    intro y hy
    exact hna ⟨f ⟨y, hy⟩, (f ⟨y, hy⟩).property⟩
theorem star_116_18 (a : Class α) (b : Class β) :
    NonemptyClass a ∨ EmptyClass b ↔ ExistsExp a b := ⟨star_116_171 a b, star_116_172 a b⟩

end PM.Architecture.Star116OpeningKernel
