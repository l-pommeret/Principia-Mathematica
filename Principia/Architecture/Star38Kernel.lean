import Principia.FirstEdition.Volume1.Star38Source

namespace PM.Architecture.Star38Kernel

abbrev Class (α : Type u) := α → Prop

def Image (f : α → β) (a : Class α) : Class β :=
  fun y => ∃ x, a x ∧ y = f x

def LeftSection (op : α → β → γ) (x : α) : β → γ := fun y => op x y
def RightSection (op : α → β → γ) (y : β) : α → γ := fun x => op x y
def Slice (op : α → β → γ) (a : Class α) (y : β) : Class γ :=
  Image (RightSection op y) a

theorem star_38_01 (op : α → β → γ) (x : α) : LeftSection op x = fun y => op x y := rfl
theorem star_38_02 (op : α → β → γ) (y : β) : RightSection op y = fun x => op x y := rfl
theorem star_38_03 (op : α → β → γ) (a : Class α) (y : β) :
    Slice op a y = Image (RightSection op y) a := rfl

theorem star_38_1 (op : α → β → γ) (x : α) (u : γ) (y : β) :
    u = LeftSection op x y ↔ u = op x y := Iff.rfl
theorem star_38_101 (op : α → β → γ) (y : β) (u : γ) (x : α) :
    u = RightSection op y x ↔ u = op x y := Iff.rfl
theorem star_38_11 (op : α → β → γ) (x : α) (y : β) :
    LeftSection op x y = RightSection op y x ∧ RightSection op y x = op x y := ⟨rfl, rfl⟩
theorem star_38_12 (op : α → β → γ) (x : α) (y : β) :
    Nonempty γ ∧ Nonempty γ := ⟨⟨op x y⟩, ⟨op x y⟩⟩
theorem star_38_13 (op : α → β → γ) (x : α) (a : Class β) (u : γ) :
    Image (LeftSection op x) a u ↔ ∃ y, a y ∧ u = op x y := Iff.rfl
theorem star_38_131 (op : α → β → γ) (y : β) (a : Class α) (u : γ) :
    Image (RightSection op y) a u ↔ ∃ x, a x ∧ u = op x y := Iff.rfl
theorem star_38_2 (op : α → β → γ) (a : Class α) (y : β) :
    Slice op a y = Image (RightSection op y) a := rfl
theorem star_38_21 (op : α → β → γ) (a : Class α) (y : β) :
    Slice op a y = fun u => ∃ x, a x ∧ u = op x y := rfl
theorem star_38_22 (op : α → β → γ) (a : Class α) (y : β) :
    Slice op a y = Image (RightSection op y) a ∧ Image (RightSection op y) a = Slice op a y := ⟨rfl, rfl⟩
theorem star_38_23 (op : α → β → γ) (a : Class α) (y : β) :
    Nonempty (Class γ) ∧ Nonempty (Class γ) := ⟨⟨Slice op a y⟩, ⟨Slice op a y⟩⟩
theorem star_38_24 (op : α → β → γ) (a : Class α) (y : β) :
    (∃ u, Slice op a y u) ↔ ∃ x, a x := by
  constructor
  · rintro ⟨u, x, hx, _⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨op x y, x, hx, rfl⟩

theorem star_38_3 (op : α → β → γ) (a : Class α) (b : Class β) :
    Image (Slice op a) b = fun c => ∃ y, b y ∧ c = Slice op a y := rfl
theorem star_38_31 (op : α → β → γ) (y : β) (k : Class (Class α)) :
    Image (fun a => Slice op a y) k = fun c => ∃ a, k a ∧ c = Image (RightSection op y) a := rfl

end PM.Architecture.Star38Kernel
