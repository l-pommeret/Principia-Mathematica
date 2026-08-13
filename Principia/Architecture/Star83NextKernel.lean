/-! Functional kernel for the second macro-lot of PM I ✱83. -/
namespace PM.Architecture.Star83NextKernel

abbrev Set (α : Type u) := α → Prop
abbrev Family (α : Type u) := Set (Set α)
def singleton (x : α) : Set α := fun y => y = x
def singletonFamily (s : Set α) : Family α := fun t => t = s
def union (k m : Family α) : Family α := fun s => k s ∨ m s
def diff (k m : Family α) : Family α := fun s => k s ∧ ¬m s
def pairwiseDisjoint (k m : Family α) : Prop := ∀ s, k s → m s → False
def Selects (k : Family α) (f : Set α → α) : Prop := ∀ ⦃s⦄, k s → s (f s)
def SelectionClass (k : Family α) : Set (Set α → α) := fun f => Selects k f
def inhabitedMembers (k : Family α) : Prop := ∀ ⦃s⦄, k s → ∃ x, s x

theorem star_83_41 (s : Set α) :
    SelectionClass (singletonFamily s) = fun f => s (f s) := by
  funext f; apply propext
  constructor
  · intro h; exact h rfl
  · intro h t ht; subst t; exact h

theorem star_83_42 (s : Set α) (f : Set α → α) :
    Selects (singletonFamily s) f ↔ s (f s) := by
  constructor
  · intro h; exact h rfl
  · intro h t ht; subst t; exact h

theorem star_83_43 (k : Family α) (hunit : ∀ ⦃s⦄, k s → ∃ x, s = singleton x)
    (f : Set α → α) (hf : Selects k f) {s : Set α} (hs : k s) :
    s = singleton (f s) := by
  obtain ⟨x, rfl⟩ := hunit hs
  funext y; apply propext
  exact ⟨fun hy => hy.trans (hf hs).symm, fun hy => hy.trans (hf hs)⟩

theorem star_83_51 (k : Family α) (f : Set α → α) (hf : Selects k f)
    (s : Set α) : Selects (diff k (singletonFamily s)) f := by
  intro t ht; exact hf ht.1

theorem star_83_52 (k : Family α) (f : Set α → α) (hf : Selects k f)
    {s : Set α} (hs : k s) {x : α} (hx : s x) :
    ∃ g, Selects k g ∧ g s = x := by
  classical
  let g := fun t => if t = s then x else f t
  refine ⟨g, ?_, by simp [g]⟩
  intro t ht
  by_cases h : t = s
  · subst t; simpa [g] using hx
  · simpa [g, h] using hf ht

theorem star_83_54 (k m : Family α) (f : Set α → α)
    (hf : Selects k f) (hg : Selects m f) : Selects (union k m) f := by
  intro s hs
  rcases hs with hs | hs
  · exact hf hs
  · exact hg hs

theorem star_83_55 (k m : Family α) (f : Set α → α)
    (hf : Selects (union k m) f) : Selects k f ∧ Selects m f := by
  exact ⟨(fun {_} h => hf (Or.inl h)), (fun {_} h => hf (Or.inr h))⟩

theorem star_83_56 (k m : Family α) :
    SelectionClass (union k m) =
      fun f => SelectionClass k f ∧ SelectionClass m f := by
  funext f; apply propext
  exact ⟨star_83_55 k m f, fun h => star_83_54 k m f h.1 h.2⟩

theorem star_83_57 (k m : Family α) (f : Set α → α) :
    Selects (union k m) f ↔ Selects k f ∧ Selects m f := by
  exact ⟨star_83_55 k m f, fun h => star_83_54 k m f h.1 h.2⟩

theorem star_83_61 (k : Family α) (f : Set α → α) (hf : Selects k f)
    {s : Set α} (hs : k s) : s (f s) := hf hs

theorem star_83_62 (k : Family α) (f : Set α → α) (hf : Selects k f) :
    ∀ ⦃s⦄, k s → ∃ x, s x := by
  intro s hs; exact ⟨f s, hf hs⟩

theorem star_83_64 (k m : Family α) (f : Set α → α) (_ : pairwiseDisjoint k m) :
    Selects (union k m) f ↔ Selects k f ∧ Selects m f := star_83_57 k m f

theorem star_83_641 (k m : Family α) (f : Set α → α)
    (_ : ∀ s t, k s → m t → ∀ x, s x → t x → False) :
    Selects (union k m) f ↔ Selects k f ∧ Selects m f := star_83_57 k m f

theorem star_83_65 (k m : Family α) (f : Set α → α)
    (hf : Selects (union k m) f) : inhabitedMembers k ∧ inhabitedMembers m := by
  constructor
  · intro s hs; exact ⟨f s, hf (Or.inl hs)⟩
  · intro s hs; exact ⟨f s, hf (Or.inr hs)⟩

theorem star_83_66 (k : Family α) (f : Set α → α) (hf : Selects k f) :
    inhabitedMembers k := star_83_62 k f hf

theorem star_83_7 (s : Set α) (f : Set α → α) (hf : Selects (singletonFamily s) f) :
    ∃ x, s x := ⟨f s, hf rfl⟩

theorem star_83_71 (s : Set α) (f : Set α → α) (hf : Selects (singletonFamily s) f) :
    singleton (f s) (f s) := rfl

theorem star_83_72 (k : Family α) (hunit : ∀ ⦃s⦄, k s → ∃ x, s = singleton x)
    (f : Set α → α) (hf : Selects k f) :
    ∀ ⦃s⦄, k s → s = singleton (f s) :=
  fun {_} hs => star_83_43 k hunit f hf hs

end PM.Architecture.Star83NextKernel
