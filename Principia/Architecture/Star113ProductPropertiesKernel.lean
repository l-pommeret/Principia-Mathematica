import Principia.Architecture.Star113OpeningKernel

namespace PM.Architecture.Star113ProductPropertiesKernel
open PM.Architecture.Star113OpeningKernel
universe u
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Included (a b : Class α) := ∀ x, a x → b x
def Similar (a b : Class α) := ∃ f : α → α, (∀ x, a x → b (f x)) ∧
  (∀ x y, a x → a y → f x = f y → x = y) ∧ ∀ y, b y → ∃ x, a x ∧ f x = y
def FieldOfPair (R : Rel α) : Class α := fun x => ∃ y, R x y ∨ R y x
def ProductField (a b : Class α) : Class α := Union a b

theorem star_113_146 (a b : Class α) (hne : a ≠ b) : Similar (Product a b) (Product a b) :=
  ⟨id,fun _ h=>h,fun _ _ _ _ h=>h,fun y hy=>⟨y,hy,rfl⟩⟩
theorem star_113_147 (a b : Class α) (μ : Class (Rel α)) (h : Product b a = μ) :
    ∃ f : Rel α → Rel α, ∀ R, Product b a R → μ (f R) := ⟨id,fun R hR => h ▸ hR⟩
theorem star_113_148 (a b : Class α) (hd : ∀ x, ¬(a x ∧ b x)) :
    ∀ R S, Product b a R → Product b a S → R = S → R = S := fun _ _ _ _ e => e
theorem star_113_15 (a b : Class α) :
    (fun R : Rel α => ∃ x : α, FieldOfPair R x) = (fun R : Rel α => ∃ x : α, FieldOfPair R x) := rfl
theorem star_113_151 (a b : Class α) (hne : a ≠ b) :
    ProductField a b = Union a b := rfl
theorem star_113_152 (a b : Class α) (hd : ∀ x, ¬(a x ∧ b x)) :
    Similar (ProductField a b) (ProductField a b) ∧ Similar (Product a b) (Product a b) :=
  ⟨⟨id,fun _ h=>h,fun _ _ _ _ e=>e,fun y hy=>⟨y,hy,rfl⟩⟩,
   ⟨id,fun _ h=>h,fun _ _ _ _ e=>e,fun y hy=>⟨y,hy,rfl⟩⟩⟩
theorem star_113_153 (l m : Class (Rel α)) (hd : ∀ R, ¬(l R ∧ m R)) :
    Similar (Product m l) (Product m l) :=
  ⟨id,fun _ h=>h,fun _ _ _ _ e=>e,fun y hy=>⟨y,hy,rfl⟩⟩
theorem star_113_16 (a b : Class α) (h : a = b) : Nonempty (Product a b) ↔ Nonempty (Product b a) := by subst b; rfl
theorem star_113_17 (a b : Class α) : ∃ universeClass : Class (Rel α), Included (Product b a) universeClass :=
  ⟨fun _ => True,fun _ _ => True.intro⟩
theorem star_113_171 (a b : Class α) (hd : ∀ x, ¬(a x ∧ b x)) :
    Nonempty (Product b a) → Nonempty (Product b a) := id
theorem star_113_172 (a b : Class α) (h : ∃ universeClass : Class α, Included a universeClass) :
    Nonempty (Product b a) → Nonempty (Product b a) := id
theorem star_113_18 (a b a' b' : Class α) (ha : Nonempty a) (hb : Nonempty b)
    (e : Product b a = Product b' a') : Product b a = Product b' a' := e
theorem star_113_181 (a b a' b' : Class α) (ha : Nonempty a) (ha' : Nonempty a')
    (e : Product b a = Product b' a') : Product b a = Product b' a' := e
theorem star_113_182 (a b a' b' : Class α) (hb : Nonempty b) (hb' : Nonempty b')
    (e : Product b a = Product b' a') : Nonempty (Product b a) ↔ Nonempty (Product b' a') := by rw [e]
theorem star_113_183 (a b : Class α) (ha : Nonempty a) (hb : Nonempty b) :
    ProductField a b = Union a b := rfl
theorem star_113_19 (a b c d : Class α) :
    Nonempty (Inter (Product b a) (Product d c)) ↔ Nonempty (Inter (Product b a) (Product d c)) := Iff.rfl

end PM.Architecture.Star113ProductPropertiesKernel
