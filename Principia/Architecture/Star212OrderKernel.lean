import Principia.Architecture.Star212MiddleKernel
namespace PM.Architecture.Star212OrderKernel
open PM.Architecture.Star212OpeningKernel PM.Architecture.Star212MiddleKernel
universe u
def Irreflexive (R : Rel α) := ∀ a, ¬R a a
def IsSeriesOn (c : Class α) (R : Rel α) :=
  Irreflexive R ∧ Transitive R ∧ ConnexOn c R ∧ ∀ a b, R a b → c a ∧ c b
def Greatest (R : Rel α) (c : Class α) (x : α) := c x ∧ ∀ y, c y → y = x ∨ R y x
def Least (R : Rel α) (c : Class α) (x : α) := c x ∧ ∀ y, c y → y = x ∨ R x y

theorem proper_irrefl : Irreflexive (@Proper α) := fun a h => h.2 (fun _ hx => hx)
theorem proper_trans : Transitive (@Proper α) := by
  rintro a b d ⟨hab,_⟩ ⟨hbd,hnd⟩; exact ⟨fun x hx => hbd x (hab x hx),fun hda => hnd (fun x hx => hab x (hda x hx))⟩
theorem star_212_23 (c : Class (Class α)) : Sigma c = fun a b => c a ∧ c b ∧ Proper a b := rfl
theorem star_212_24 (sections : Class (Class α)) : Sigma sections = fun a b => sections a ∧ sections b ∧ Proper a b := rfl
theorem star_212_25 (c : Class (Class α)) (a b : Class α) : Sigma c a b → Proper a b := fun h => h.2.2
theorem star_212_3 (c : Class (Class α)) (hc : ConnexOn c Proper) : IsSeriesOn c (Sgm c) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact star_212_155 c
  · rintro a b d hab hbd; exact ⟨hab.1,hbd.2.1,proper_trans a b d hab.2.2 hbd.2.2⟩
  · intro a b ha hb
    rcases hc a b ha hb with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨ha,hb,h⟩)
    · exact Or.inr (Or.inr ⟨hb,ha,h⟩)
  · intro a b h; exact ⟨h.1,h.2.1⟩
theorem star_212_31 (c : Class (Class α)) (hc : ConnexOn c Proper) : IsSeriesOn c (Sigma c) := star_212_3 c hc
theorem star_212_32 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : Greatest R c x := h
theorem star_212_321 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : c x := h.1
theorem star_212_322 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : ∀ y, c y → y = x ∨ R y x := h.2
theorem star_212_33 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : Least R c x := h
theorem star_212_331 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : c x := h.1
theorem star_212_34 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : ∀ y, c y → y = x ∨ R x y := h.2
theorem star_212_35 (sections : Class (Class α)) (a b : Class α) : Sigma sections a b → sections a ∧ sections b := fun h => ⟨h.1,h.2.1⟩
theorem star_212_36 (sections : Class (Class α)) (a : Class α) : Dom (Sgm sections) a → ∃ b, Sgm sections a b := fun h => h
theorem star_212_4 (c : Class (Class α)) (a : Class α) (h : Greatest (Sigma c) c a) : Greatest (Sigma c) c a := h
theorem star_212_401 (c : Class (Class α)) (a : Class α) (h : Greatest (Sigma c) c a) : c a := h.1
theorem star_212_402 (c : Class (Class α)) (a : Class α) (h : Greatest (Sigma c) c a) : ∀ b, c b → b = a ∨ Sigma c b a := h.2
end PM.Architecture.Star212OrderKernel
