import Principia.Architecture.Star52NextKernel

namespace PM.Architecture.Star52CompletionKernel

open PM.Architecture.Star52OpeningKernel
open PM.Architecture.Star52NextKernel

def Included (A B : Class α) := ∀ {x}, A x → B x
def Intersection (A B : Class α) : Class α := fun x => A x ∧ B x
def Union (A B : Class α) : Class α := fun x => A x ∨ B x
def Difference (A B : Class α) : Class α := fun x => A x ∧ ¬ B x
def Null (α : Sort u) : Class α := fun _ => False
def atMostOne (A : Class α) := ∀ x y, A x → A y → x = y

theorem star_52_22 (x : α) : unitClasses α (singleton x) := ⟨x, rfl⟩

theorem star_52_23 [Nonempty α] :
    (∃ A, unitClasses α A) ∧ ∃ A, ¬ unitClasses α A := by
  classical
  let x := Classical.choice (inferInstance : Nonempty α)
  exact ⟨⟨singleton x, star_52_22 x⟩, ⟨Null α, star_52_21⟩⟩

theorem star_52_24 [Nonempty α] :
    unitClasses α ≠ Null (Class α) ∧
      (fun A => ¬ unitClasses α A) ≠ Null (Class α) := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := star_52_23 (α := α)
  constructor
  · intro e; have he := congrFun e A; exact Eq.mp he hA
  · intro e; have he := congrFun e B; exact Eq.mp he hB

theorem star_52_3 (A : Class α) :
    Included (fun B => ∃ x, A x ∧ B = singleton x) (unitClasses α) := by
  rintro B ⟨x, _, rfl⟩
  exact star_52_22 x

theorem star_52_31 (K : Class (Class α)) :
    Included K (unitClasses α) ↔
      ∃ A : Class α, K = fun B => ∃ x, A x ∧ B = singleton x := by
  constructor
  · intro h
    refine ⟨fun x => K (singleton x), ?_⟩
    funext B; apply propext; constructor
    · intro hB
      obtain ⟨x, rfl⟩ := h hB
      exact ⟨x, hB, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  · rintro ⟨A, rfl⟩
    exact star_52_3 A

theorem star_52_4 (A : Class α) :
    (unitClasses α A ∨ A = Null α) ↔ atMostOne A := by
  constructor
  · rintro (h | rfl)
    · exact (star_52_16 A).1 h |>.2
    · intro x y hx; exact False.elim hx
  · intro h
    classical
    by_cases inhabited : ∃ x, A x
    · left; exact (star_52_16 A).2 ⟨inhabited, h⟩
    · right; funext x; apply propext; exact ⟨fun hx => inhabited ⟨x, hx⟩, False.elim⟩

theorem star_52_41 (A : Class α) :
    (¬ atMostOne A) ↔ ∃ x y, A x ∧ A y ∧ x ≠ y := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    intro x y hx hy
    apply Classical.byContradiction
    intro hxy
    exact hn ⟨x,y,hx,hy,hxy⟩
  · rintro ⟨x,y,hx,hy,hne⟩ h
    exact hne (h x y hx hy)

theorem star_52_42 (hA : unitClasses α A) :
    inhabitedClass (Intersection A B) ↔ unitClasses α (Intersection A B) := by
  obtain ⟨x, rfl⟩ := hA
  constructor
  · rintro ⟨y, hy, hB⟩
    have yx : y = x := hy
    subst y
    exact ⟨x, by funext z; apply propext; exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz ▸ hB⟩⟩⟩
  · exact fun h => (star_52_16 _).1 h |>.1

theorem star_52_43 :
    unitClasses α A ∧ inhabitedClass (Intersection A B) ↔
      unitClasses α A ∧ unitClasses α (Intersection A B) := by
  constructor
  · rintro ⟨hA,h⟩; exact ⟨hA, (star_52_42 hA).mp h⟩
  · rintro ⟨hA,h⟩; exact ⟨hA, (star_52_42 hA).mpr h⟩

theorem star_52_44 (hA : unitClasses α A) :
    inhabitedClass (Intersection A B) ↔ Included A B ∧ Intersection A B = A := by
  obtain ⟨x, rfl⟩ := hA
  constructor
  · rintro ⟨y, hy, hB⟩
    have yx : y = x := hy
    subst y
    constructor
    · intro z hz; exact hz ▸ hB
    · funext z; apply propext; exact ⟨And.left, fun hz => ⟨hz, hz ▸ hB⟩⟩
  · rintro ⟨h,_⟩; exact ⟨x, rfl, h rfl⟩

theorem star_52_45 (hA : unitClasses α A) (hB : unitClasses α B) :
    Included A (Union B C) ↔ A = B ∨ Included A C := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  constructor
  · intro h
    rcases h rfl with hab | hC
    · left; subst b; rfl
    · right; intro x hx; exact hx ▸ hC
  · rintro (e | h)
    · exact fun hx => Or.inl (e ▸ hx)
    · exact fun hx => Or.inr (h hx)

theorem star_52_46 (hA : unitClasses α A) (hB : unitClasses α B) :
    Included A B ↔ A = B ∧ inhabitedClass (Intersection A B) := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  constructor
  · intro h; have e : a = b := h rfl; subst b; exact ⟨rfl, ⟨a,rfl,rfl⟩⟩
  · rintro ⟨e,_⟩; exact fun hx => e ▸ hx

theorem star_52_6 (hA : unitClasses α A) (x : α) :
    A x ↔ singleton x = A ∧ uniqueMember A x := by
  obtain ⟨a, rfl⟩ := hA
  constructor
  · intro hx
    have xa : x = a := hx
    subst x
    exact ⟨rfl, rfl, fun y hy => hy⟩
  · exact fun h => h.2.1

theorem star_52_601 (hA : unitClasses α A) (P : α → Prop) :
    (∃ x, uniqueMember A x ∧ P x) ↔ (∀ x, A x → P x) ∧ ∃ x, A x ∧ P x := by
  obtain ⟨a, rfl⟩ := hA
  constructor
  · rintro ⟨x, ⟨hx, _⟩, hP⟩
    have xa : x = a := hx; subst x
    exact ⟨fun y hy => hy ▸ hP, ⟨a,rfl,hP⟩⟩
  · rintro ⟨all, ⟨x,hx,_⟩⟩
    have xa : x = a := hx; subst x
    exact ⟨a, ⟨rfl, fun y hy => hy⟩, all a rfl⟩

theorem star_52_602 (hφ : unitClasses α φ) (P : α → Prop) :
    (∃ x, uniqueMember φ x ∧ P x) ↔ (∀ x, φ x → P x) ∧ ∃ x, φ x ∧ P x :=
  star_52_601 hφ P

theorem star_52_61 (hA : unitClasses α A) :
    (∃ x, uniqueMember A x ∧ B x) ↔ Included A B ∧ inhabitedClass (Intersection A B) := by
  obtain ⟨a, rfl⟩ := hA
  constructor
  · rintro ⟨x, ⟨hx,_⟩, hB⟩
    have xa : x = a := hx; subst x
    exact ⟨fun hx => hx ▸ hB, ⟨a,rfl,hB⟩⟩
  · rintro ⟨inc, ⟨x,hx,hB⟩⟩
    have xa : x = a := hx; subst x
    exact ⟨a, ⟨rfl, fun y hy => hy⟩, inc rfl⟩

theorem star_52_62 (hA : unitClasses α A) (hB : unitClasses α B) :
    A = B ↔ ∀ x y, uniqueMember A x → uniqueMember B y → x = y := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  constructor
  · intro equality x y hx hy
    have xa : x = a := hx.1
    have yb : y = b := hy.1
    subst x; subst y
    have : singleton a a ↔ singleton b a := Iff.of_eq (congrFun equality a)
    exact this.mp rfl
  · intro values
    have ab := values a b ⟨rfl, fun y hy => hy⟩ ⟨rfl, fun y hy => hy⟩
    subst b; rfl

theorem star_52_63 (hA : unitClasses α A) (hB : unitClasses α B) (hne : A ≠ B) :
    Intersection A B = Null α := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  funext x; apply propext; constructor
  · rintro ⟨rfl, e⟩; exact hne (e ▸ rfl)
  · exact False.elim

theorem star_52_64 (hA : unitClasses α A) :
    unitClasses α (Intersection A B) ∨ Intersection A B = Null α := by
  apply (star_52_4 _).2
  exact fun x y hx hy => (star_52_16 A).1 hA |>.2 x y hx.1 hy.1

theorem star_52_7 (h : unitClasses α (Difference B A))
    (hAX : Included A X) (hXB : Included X B) : X = A ∨ X = B := by
  obtain ⟨d, hd⟩ := h
  classical
  by_cases hDX : X d
  · right
    funext x; apply propext; refine ⟨hXB, ?_⟩
    intro hx
    by_cases hxa : A x
    · exact hAX hxa
    · have : Difference B A x := ⟨hx,hxa⟩
      have xd : x = d := by rw [hd] at this; exact this
      exact xd ▸ hDX
  · left
    funext x; apply propext; refine ⟨?_, hAX⟩
    intro hx
    apply Classical.byContradiction
    intro hxa
    have : Difference B A x := ⟨hXB hx, hxa⟩
    rw [hd] at this
    exact hDX (this ▸ hx)

end PM.Architecture.Star52CompletionKernel
