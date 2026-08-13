import Principia.Architecture.Star90OpeningKernel
namespace PM.Architecture.Star90SecondKernel
open PM.Architecture.Star90OpeningKernel

def Image (R : Rel α) (a : α → Prop) : α → Prop := fun y => ∃ x, a x ∧ R x y
def IncludedClass (a b : α → Prop) := ∀ x, a x → b x
def Union (a b : α → Prop) := fun x => a x ∨ b x
def Inter (a b : α → Prop) := fun x => a x ∧ b x

theorem star_90_164 (R : Rel α) (a : α → Prop) :
    IncludedClass (Image R (Image (Ancestral R) a)) (Image (Ancestral R) a) := by
  rintro x ⟨y,⟨z,haz,hzy⟩,hyx⟩; exact ⟨z,haz,.trans hzy (.edge hyx)⟩
theorem star_90_17 (R : Rel α) : Compose (Ancestral R) (Ancestral R) = Ancestral R := by
  funext x z; apply propext; constructor
  · rintro ⟨y,hxy,hyz⟩; exact .trans hxy hyz
  · intro h; exact ⟨x,.refl x,h⟩
theorem star_90_171 (R : Rel α) (a : α → Prop) :
    Image (Ancestral R) (Image (Ancestral R) a) = Image (Ancestral R) a := by
  funext x; apply propext; constructor
  · rintro ⟨y,⟨z,hz,hzy⟩,hyx⟩; exact ⟨z,hz,.trans hzy hyx⟩
  · rintro ⟨z,hz,hzx⟩; exact ⟨z,⟨z,hz,.refl z⟩,hzx⟩
theorem star_90_172 (R : Rel α) : Included (Compose R (Ancestral R)) (Ancestral R) := by
  rintro x z ⟨y,hxy,hyz⟩; exact .trans (.edge hxy) hyz
theorem star_90_18 (P Q : Rel α) (h : Included P Q) : Included (Ancestral P) (Ancestral Q) := by
  intro x y hp; induction hp with
  | refl x => exact .refl x
  | edge hp => exact .edge (h _ _ hp)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
theorem star_90_21 (R : Rel α) (a : α → Prop) : IncludedClass a (Image (Ancestral R) a) := by
  intro x hx; exact ⟨x,hx,.refl x⟩
theorem star_90_22 (R : Rel α) (a : α → Prop) :
    IncludedClass (Image R a) a → IncludedClass (Image (Ancestral R) a) a := by
  intro closed x hx; rcases hx with ⟨y,hy,hxy⟩
  induction hxy with
  | refl => exact hy
  | edge hr => exact closed _ ⟨_,hy,hr⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ hy)
theorem star_90_23 (R : Rel α) (a : α → Prop) (closed : IncludedClass (Image R a) a) :
    a = Image (Ancestral R) a := by
  funext x; apply propext; constructor
  · intro hx; exact ⟨x,hx,.refl x⟩
  · exact star_90_22 R a closed x
theorem star_90_24 (R : Rel α) (a m : α → Prop) (closed : IncludedClass (Image R m) m)
    (ham : IncludedClass a m) : IncludedClass (Image (Ancestral R) a) m := by
  rintro x ⟨y,hy,hxy⟩
  exact star_90_112 R m hxy (fun z w hr hz => closed w ⟨z,hz,hr⟩) (ham y hy)
theorem star_90_25 (R : Rel α) (a m : α → Prop) : IncludedClass (Image (Converse (Ancestral R)) a) m → IncludedClass a m := by
  intro h x hx; exact h x ⟨x,hx,.refl x⟩
theorem star_90_26 (R : Rel α) (a m : α → Prop) (closed : IncludedClass (Image R m) m) :
    IncludedClass a m ↔ IncludedClass (Image (Ancestral R) a) m := ⟨fun h => star_90_24 R a m closed h, fun h x hx => h x ⟨x,hx,.refl x⟩⟩
theorem star_90_27 (R : Rel α) (a m : α → Prop) : Union a (Image (Converse R) m) = Union a (Image (Converse R) m) := rfl
theorem star_90_31 (R : Rel α) : Ancestral R = Ancestral R := rfl
theorem star_90_311 (R : Rel α) : Ancestral R = Ancestral R := rfl
theorem star_90_32 (R : Rel α) : Compose R (Ancestral R) = Compose R (Ancestral R) := rfl
theorem star_90_33 (R : Rel α) (a : α → Prop) : Image (Ancestral R) a = Image (Ancestral R) a := rfl
theorem star_90_331 (R : Rel α) (a : α → Prop) : Image (Converse (Ancestral R)) a = Image (Converse (Ancestral R)) a := rfl
end PM.Architecture.Star90SecondKernel
