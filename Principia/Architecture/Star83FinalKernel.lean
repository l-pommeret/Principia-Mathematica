/-! Functional kernel for the seven final propositions of PM I ✱83. -/
namespace PM.Architecture.Star83FinalKernel

abbrev Set (α : Type u) := α → Prop
abbrev Family (α : Type u) := Set (Set α)
def empty : Family α := fun _ => False
def singleton (x : α) : Set α := fun y => y = x
def singletonFamily (s : Set α) : Family α := fun t => t = s
def union (k m : Family α) : Family α := fun s => k s ∨ m s
def Selects (k : Family α) (f : Set α → α) : Prop := ∀ ⦃s⦄, k s → s (f s)
def HasSelection (k : Family α) : Prop := ∃ f, Selects k f
def allInhabited (k : Family α) : Prop := ∀ ⦃s⦄, k s → ∃ x, s x

theorem star_83_73 (k m : Family α) (f : Set α → α) :
    Selects (union k m) f ↔ Selects k f ∧ Selects m f := by
  constructor
  · intro h
    exact ⟨(fun {_} hs => h (Or.inl hs)), (fun {_} hs => h (Or.inr hs))⟩
  · rintro ⟨hk, hm⟩ s (hs | hs)
    · exact hk hs
    · exact hm hs

theorem star_83_8 (k : Family α) (f : Set α → α) (hf : Selects k f) :
    allInhabited k := by
  intro s hs
  exact ⟨f s, hf hs⟩

theorem star_83_9 [Inhabited α] : HasSelection (empty : Family α) := by
  exact ⟨fun _ => default, fun _ h => False.elim h⟩

theorem star_83_901 (s : Set α) :
    HasSelection (singletonFamily s) ↔ ∃ x, s x := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f s, hf rfl⟩
  · rintro ⟨x, hx⟩
    classical
    exact ⟨fun t => if t = s then x else x, fun t ht => by subst t; simpa using hx⟩

theorem star_83_902 (k m : Family α) :
    HasSelection (union k m) → HasSelection k ∧ HasSelection m := by
  rintro ⟨f, hf⟩
  exact ⟨⟨f, (star_83_73 k m f).mp hf |>.1⟩,
    ⟨f, (star_83_73 k m f).mp hf |>.2⟩⟩

theorem star_83_903 (s t : Set α) :
    HasSelection (union (singletonFamily s) (singletonFamily t)) →
      (∃ x, s x) ∧ ∃ y, t y := by
  intro h
  have hm := star_83_902 (singletonFamily s) (singletonFamily t) h
  exact ⟨(star_83_901 s).mp hm.1, (star_83_901 t).mp hm.2⟩

theorem star_83_904 (k : Family α) (s : Set α) :
    HasSelection (union k (singletonFamily s)) →
      HasSelection k ∧ ∃ x, s x := by
  intro h
  have hm := star_83_902 k (singletonFamily s) h
  exact ⟨hm.1, (star_83_901 s).mp hm.2⟩

end PM.Architecture.Star83FinalKernel
