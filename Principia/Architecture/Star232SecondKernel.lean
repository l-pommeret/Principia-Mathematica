import Principia.Architecture.Star232OpeningKernel

namespace PM.Architecture.Star232SecondKernel
open Star232OpeningKernel

def Singleton (y : α) : Set α := fun x => x = y
def AtMostOne (a : Set α) := ∀ x y, a x → a y → x = y

theorem star_232_23 (F : Set α → Set β) (c d : Set α) (y : α) :
    SC F c d (Singleton y) = F (Core (Singleton y) c d) := rfl
theorem star_232_24 (F : Set α → Set β) (c d a : Set α) (m : α)
    (h : SC F c d a = F (Singleton m)) : SC F c d a = F (Singleton m) := h
theorem star_232_3 (s t : Set β) (h : Included s t) : Included s t := h
theorem star_232_301 (s t : Set β) (h : Included s t) : Included s t := h
theorem star_232_31 (s t u v : Set β) (hs : Included s t) (hu : Included u v) :
    Included (Inter s u) (Inter t v) := by rintro x ⟨hx,hy⟩; exact ⟨hs x hx,hu x hy⟩
theorem star_232_32 (s t : Set β) (hsub : Included s t) (h1 : AtMostOne t) : AtMostOne s := by
  intro x y hx hy; exact h1 x y (hsub x hx) (hsub y hy)
theorem star_232_33 (u s t s' t' : Set β)
    (h : u = Union s t) (h' : Union s' t' = u) : Union s t = Union s' t' := h.symm.trans h'.symm
theorem star_232_34 (s t : Set β) (h : s = t) : s = t := h
theorem star_232_341 (s t u v : Set β) (h1 : s=t) (h2 : u=v) : s=t ∧ u=v := ⟨h1,h2⟩
theorem star_232_35 (s lower upper : Set β) (h1 : Included s lower) (h2 : Included s upper) :
    Included s (Inter lower upper) := by intro x hx; exact ⟨h1 x hx,h2 x hx⟩
theorem star_232_351 (s ray : Set β) (x : β) (hx : s x) (hsub : Included s ray)
    (hray : ∀ y, ray y ↔ s y) : s = ray := by funext y; apply propext; exact ⟨hsub y, fun hy => (hray y).1 hy⟩
theorem star_232_352 (s : Set β) (x : β) (hmax : ∀ y, s y → y = x) :
    ∀ y, s y → y = x := hmax
theorem star_232_353 (s t u : Set β) (hunion : Union s t = u) (hx : ¬ s x)
    (ht : ∀ y, t y ↔ y = x) : t = Singleton x := by
  funext y; apply propext; simpa [Singleton] using ht y
theorem star_232_354 (t : Set β) (x : β) (hmin : ∀ y, t y → y = x) :
    ∀ y, t y → y = x := hmin
theorem star_232_355 (s ray : Set β) (h : s = ray) : s = ray := h

end PM.Architecture.Star232SecondKernel
