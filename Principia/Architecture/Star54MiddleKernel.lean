import Principia.Architecture.Star54OpeningKernel

namespace PM.Architecture.Star54MiddleKernel
open PM.Architecture.Star54OpeningKernel
local notation "∅ᶜ" => PM.Architecture.Star54OpeningKernel.Empty
local notation "⟪" x "⟫" => PM.Architecture.Star54OpeningKernel.Singleton x

def Included (a b : Class Object) := ∀ x, a x → b x
def Inter (a b : Class Object) : Class Object := fun x => a x ∧ b x
def Union (a b : Class Object) : Class Object := fun x => a x ∨ b x
def Diff (a b : Class Object) : Class Object := fun x => a x ∧ ¬ b x

theorem star_54_271 (a : Class Object) :
    (One a ∨ Two a) ↔ ∃ x y, a = Pair x y := by
  constructor
  · rintro (⟨x,rfl⟩ | ⟨x,y,_,rfl⟩)
    · exact ⟨x,x, by apply class_ext; intro z; exact ⟨Or.inl, fun h => h.elim id id⟩⟩
    · exact ⟨x,y,rfl⟩
  · rintro ⟨x,y,rfl⟩
    exact star_54_27 x y

theorem star_54_3 (a : Class Object) :
    Two a ↔ ∃ x, a x ∧ One (Diff a (Singleton x)) := by
  classical
  constructor
  · rintro ⟨x,y,hxy,rfl⟩
    refine ⟨x, Or.inl rfl, y, ?_⟩
    apply class_ext
    intro z
    constructor
    · rintro ⟨hzx|hzy, hn⟩
      · exact (hn hzx).elim
      · exact hzy
    · intro hzy
      exact ⟨Or.inr hzy, fun hzx => hxy (hzx.symm.trans hzy)⟩
  · rintro ⟨x,hax,y,hd⟩
    have hay : a y := by
      have hy : Diff a (⟪x⟫) y := by rw [hd]; rfl
      exact hy.1
    refine ⟨x,y, ?_, ?_⟩
    · intro hxy; subst y
      have : Diff a (Singleton x) x := by rw [hd]; rfl
      exact this.2 rfl
    · apply class_ext
      intro z
      constructor
      · intro haz
        by_cases hzx : z = x
        · exact Or.inl hzx
        · have : Diff a (Singleton x) z := ⟨haz,hzx⟩
          rw [hd] at this
          exact Or.inr this
      · rintro (rfl|rfl)
        · exact hax
        · exact hay

theorem star_54_4 (x y : Object) (b : Class Object) :
    Included b (Pair x y) ↔ b = ∅ᶜ ∨ b = ⟪x⟫ ∨ b = ⟪y⟫ ∨ b = Pair x y := by
  classical
  constructor
  · intro h
    by_cases hx : b x
    · by_cases hy : b y
      · exact Or.inr (Or.inr (Or.inr (by apply class_ext; intro z; exact ⟨h z, fun hz => hz.elim (fun e => e▸hx) (fun e => e▸hy)⟩)))
      · exact Or.inr (Or.inl (by apply class_ext; intro z; constructor; intro hz; rcases h z hz with e|e; exact e; exact (hy (e▸hz)).elim; intro e; exact e▸hx))
    · by_cases hy : b y
      · exact Or.inr (Or.inr (Or.inl (by apply class_ext; intro z; constructor; intro hz; rcases h z hz with e|e; exact (hx (e▸hz)).elim; exact e; intro e; exact e▸hy)))
      · exact Or.inl (by apply class_ext; intro z; exact ⟨fun hz => (h z hz).elim (fun e => hx (e▸hz)) (fun e => hy (e▸hz)), False.elim⟩)
  · rintro (rfl|rfl|rfl|rfl) <;> simp [Included,
      PM.Architecture.Star54OpeningKernel.Empty,
      PM.Architecture.Star54OpeningKernel.Singleton, Pair]

theorem star_54_41 (a b : Class Object) : Two a → Included b a → b=∅ᶜ ∨ One b ∨ Two b := by
  rintro ⟨x,y,h,rfl⟩ hb
  rcases (star_54_4 x y b).mp hb with rfl|rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨x,rfl⟩)
  · exact Or.inr (Or.inl ⟨y,rfl⟩)
  · exact Or.inr (Or.inr ⟨x,y,h,rfl⟩)

theorem star_54_411 (a b : Class Object) : Two a → Included b a → (Zero b ∨ One b ∨ Two b) := by
  intro ha hb
  rcases star_54_41 a b ha hb with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem star_54_42 (a b : Class Object) : Two a → Included b a → b≠∅ᶜ → One b ∨ Two b := by
  intro ha hb hn
  rcases star_54_41 a b ha hb with h|h|h
  · exact (hn h).elim
  · exact Or.inl h
  · exact Or.inr h

theorem star_54_43 (a b : Class Object) : One a → One b →
    (Inter a b = ∅ᶜ ↔ Two (Union a b)) := by
  rintro ⟨x,hax⟩ ⟨y,hby⟩
  subst a
  subst b
  constructor
  · intro h
    have hxy : x ≠ y := fun e => by
      subst y
      have hx : Inter (⟪x⟫) (⟪x⟫) x := ⟨rfl,rfl⟩
      rw [h] at hx
      exact hx
    exact ⟨x,y,hxy,by apply class_ext; intro z; rfl⟩
  · intro htwo
    have hxy : x ≠ y := by
      rw [← star_54_26 x y]
      simpa only [Union, PM.Architecture.Star54OpeningKernel.Singleton, Pair] using htwo
    apply class_ext; intro z; constructor
    · rintro ⟨hzx,hzy⟩
      exact hxy (hzx.symm.trans hzy)
    · exact False.elim

theorem star_54_44 (x y z w : Object) (hzw : z≠w) (hz : Pair x y z) (hw : Pair x y w) :
    (z=x∧w=y)∨(z=y∧w=x) := by
  rcases hz with rfl|rfl <;> rcases hw with rfl|rfl
  · exact (hzw rfl).elim
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact (hzw rfl).elim

theorem star_54_441 (x y z w : Object) (hzw:z≠w) (hz:Pair x y z) (hw:Pair x y w) :
    (z=x∧w=y)∨(z=y∧w=x) := star_54_44 x y z w hzw hz hw

theorem star_54_442 (x y z w : Object) (hxy:x≠y) (hzw:z≠w) (hz:Pair x y z) (hw:Pair x y w) :
    (z=x∧w=y)∨(z=y∧w=x) := star_54_44 x y z w hzw hz hw

end PM.Architecture.Star54MiddleKernel
