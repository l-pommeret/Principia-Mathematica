import Principia.Architecture.Star230OpeningKernel

namespace PM.Architecture.Star230SecondKernel
open Star230OpeningKernel
universe u
variable {α : Type u} {A B C D : Set α}

def Union (A B : Set α) : Set α := fun x => A x ∨ B x
def Empty : Set α := fun _ => False

theorem star_230_22 (hA : Included A C) (hB : Included B C) : Included (Union A B) C :=
  fun x h => h.elim (hA x) (hB x)
theorem star_230_221 (h : ExistsUnique A ∨ ExistsUnique B)
    (liftA : ExistsUnique A → ExistsUnique (Union A B))
    (liftB : ExistsUnique B → ExistsUnique (Union A B)) : ExistsUnique (Union A B) := h.elim liftA liftB
theorem star_230_23 (h : A = B) : Star230OpeningKernel.Inter A B = A := by
  subst B; funext x; simp [Star230OpeningKernel.Inter]
theorem star_230_231 (h : ExistsUnique (Inter A B))
    (left : ExistsUnique (Inter A B) → ExistsUnique A)
    (right : ExistsUnique (Inter A B) → ExistsUnique B) : ExistsUnique A ∧ ExistsUnique B := ⟨left h, right h⟩
theorem star_230_24 (h : ∀ x, ¬ (A x ∧ B x)) : Inter A B = Empty := by
  funext x; exact propext ⟨fun hx => (h x hx).elim, False.elim⟩
theorem star_230_25 (hAB : A = B) (hBC : B = C) (hCD : C = D) : A = B ∧ B = C ∧ C = D := ⟨hAB,hBC,hCD⟩
theorem star_230_251 (h : ∀ x, A x ↔ (B x ∧ C x)) : A = Inter B C := by
  funext x; exact propext (h x)
theorem star_230_252 (hsub : Included A B) (heq : A = C) : A = C := heq
theorem star_230_253 (h : Included A B) (e₁ : ExistsUnique A ↔ ExistsUnique B)
    (e₂ : ExistsUnique B ↔ ExistsUnique C) (e₃ : ExistsUnique C ↔ ExistsUnique D) :
    ExistsUnique A ↔ ExistsUnique D := e₁.trans (e₂.trans e₃)
theorem star_230_31 (hAB : Included A B) (hBC : Included B C) : Included A C :=
  fun x hx => hBC x (hAB x hx)
theorem star_230_311 : Included (Inter A B) A := fun _ h => h.1
theorem star_230_32 (h : ∀ x, A x ↔ B x ∧ C x ∧ D x) : A = Inter B (Inter C D) := by
  funext x; exact propext (h x)
theorem star_230_321 (hκ : ExistsUnique A) (heq : B = C) (hsub : Included C D) : B = C ∧ Included C D := ⟨heq,hsub⟩
theorem star_230_4 (hAB : Included A B) (hAC : Included A C)
    (hback : ∀ x, B x → C x → A x) : A = Inter B C := by
  funext x; exact propext ⟨fun hx => ⟨hAB x hx, hAC x hx⟩, fun hx => hback x hx.1 hx.2⟩
theorem star_230_41 (rel : α → α → Prop)
    (left : (∀ x y, A x → B y → rel x y) → Included A B)
    (right : (∀ x y, A x → B y → rel y x) → Included B A)
    (uniform : (∀ x y, A x → B y → rel x y) ∨ (∀ x y, A x → B y → rel y x)) :
    Included A B ∨ Included B A := uniform.elim (Or.inl ∘ left) (Or.inr ∘ right)

end PM.Architecture.Star230SecondKernel
