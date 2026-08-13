/-! Functional, simple-type kernel for PM I ✱83, first macro-lot. -/

namespace PM.Architecture.Star83Kernel

abbrev Set (α : Type u) := α → Prop
abbrev Family (α : Type u) := Set (Set α)

def empty : Set α := fun _ => False
def singleton (x : α) : Set α := fun y => y = x
def union (κ mu : Family α) : Family α := fun s => κ s ∨ mu s
def disjoint (κ mu : Family α) : Prop := ∀ s, κ s → mu s → False
def Selects (κ : Family α) (f : Set α → α) : Prop :=
  ∀ ⦃s⦄, κ s → s (f s)
def SelectionClass (κ : Family α) : Set (Set α → α) := fun f => Selects κ f

theorem star_83_1 (κ : Family α) (f : Set α → α) :
    Selects κ f → ¬ κ empty := by
  intro hf he
  exact hf he

theorem star_83_11 (κ : Family α) (he : κ empty) :
    SelectionClass κ = empty := by
  funext f
  apply propext
  exact ⟨fun hf => star_83_1 κ f hf he, False.elim⟩

theorem star_83_12 (κ : Family α) (f : Set α → α) :
    SelectionClass κ f ↔ Selects κ f := Iff.rfl

theorem star_83_13 (κ : Family α) (f : Set α → α) (hne : ¬ κ empty) :
    SelectionClass κ f ↔ ∀ ⦃s⦄, κ s → s (f s) := by
  exact Iff.rfl

theorem star_83_14 (κ : Family α) (f : Set α → α)
    (h : ∀ ⦃s⦄, κ s → s (f s)) : SelectionClass κ f := h

theorem star_83_15 : SelectionClass (empty : Family α) = fun _ => True := by
  funext f
  apply propext
  exact ⟨fun _ => True.intro, fun _ _ h => False.elim h⟩

theorem star_83_16 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ¬ κ empty := star_83_1 κ f hf

theorem star_83_2 (κ : Family α) (f : Set α → α) (hf : Selects κ f) {s : Set α} :
    κ s → s (f s) := fun hs => hf hs

theorem star_83_21 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ∀ ⦃s⦄, κ s → ∃ x, s x := by
  intro s hs
  exact ⟨f s, hf hs⟩

theorem star_83_22 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ∀ ⦃s⦄, κ s → ∃ x, x = f s ∧ ∀ y, y = f s → y = x := by
  intro s _
  exact ⟨f s, rfl, fun y hy => hy⟩

theorem star_83_23 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ∀ x, (∃ s, κ s ∧ x = f s) ↔ ∃ s, κ s ∧ x = f s := fun _ => Iff.rfl

theorem star_83_24 (κ : Family α) (f : Set α → α) (hf : Selects κ f)
    {s : Set α} (hs : κ s) {x : α} (hx : s x) :
    ∃ g : Set α → α, Selects κ g ∧ g s = x := by
  classical
  let g : Set α → α := fun t => if t = s then x else f t
  refine ⟨g, ?_, by simp [g]⟩
  intro t ht
  by_cases hts : t = s
  · subst t
    simpa [g] using hx
  · simpa [g, hts] using hf ht

theorem star_83_25 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ∀ ⦃s⦄, κ s → s (f s) := hf

theorem star_83_26 (κ : Family α) (f : Set α → α) :
    (∀ ⦃s⦄, κ s → s (f s)) → SelectionClass κ f := fun h => h

theorem star_83_271 (κ : Family α) (f : Set α → α) (hf : Selects κ f) :
    ∀ ⦃s⦄, κ s → s (f s) := hf

theorem star_83_29 (κ : Family α) (f : Set α → α) :
    SelectionClass κ f ↔ ∀ ⦃s⦄, κ s → s (f s) := Iff.rfl

theorem star_83_3 (κ mu : Family α) (f : Set α → α) :
    Selects (union κ mu) f ↔ Selects κ f ∧ Selects mu f := by
  constructor
  · intro h
    exact ⟨(fun {_} hs => h (Or.inl hs)), (fun {_} hs => h (Or.inr hs))⟩
  · rintro ⟨hk, hl⟩ s (hs | hs)
    · exact hk hs
    · exact hl hs

theorem star_83_31 (κ mu : Family α) (f : Set α → α) (_ : disjoint κ mu) :
    SelectionClass (union κ mu) f ↔
      SelectionClass κ f ∧ SelectionClass mu f := star_83_3 κ mu f

end PM.Architecture.Star83Kernel
