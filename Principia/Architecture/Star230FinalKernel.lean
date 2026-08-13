import Principia.Architecture.Star230SecondKernel

namespace PM.Architecture.Star230FinalKernel
open Star230OpeningKernel
universe u
variable {α : Type u} {A B C D : Set α}

theorem star_230_42
    (forward : ExistsUnique A → ExistsUnique B → ExistsUnique (Inter A B))
    (left : ExistsUnique (Inter A B) → ExistsUnique A)
    (right : ExistsUnique (Inter A B) → ExistsUnique B) :
    ExistsUnique A ∧ ExistsUnique B ↔ ExistsUnique (Inter A B) :=
  ⟨fun h => forward h.1 h.2, fun h => ⟨left h, right h⟩⟩
theorem star_230_421 (empty : Inter A B = fun _ => False)
    (ha : ExistsUnique A) (hb : ExistsUnique B)
    (contra : ExistsUnique A → ExistsUnique B → Inter A B ≠ fun _ => False) : False := contra ha hb empty
theorem star_230_51 (hAC : Included A C) (hCB : Included C B) : Included A B :=
  fun x hx => hCB x (hAC x hx)
theorem star_230_511 (hy : A x) (fiber : ∀ y, A y → B = A) : B = A := fiber x hy
theorem star_230_512 (h : Included A B) (map : Included A B → Included C D) : Included C D := map h
theorem star_230_513 (hq : ExistsUnique A) (e : Included B C ↔ Included D A) : Included B C ↔ Included D A := e
theorem star_230_514 (hq : ExistsUnique A) (hu : ExistsUnique B)
    (hsub : Included C D) (converges : ExistsUnique A → ExistsUnique B → Included C D → ExistsUnique D) :
    ExistsUnique D := converges hq hu hsub
theorem star_230_52 (hf : ExistsUnique A) (hg : ExistsUnique B) (h : Included C D)
    (lift : ExistsUnique A → ExistsUnique B → Included C D → D x) : D x := lift hf hg h
theorem star_230_53 (order : Prop) (maximum : Prop)
    (forward : order → maximum → ExistsUnique A → Included B C)
    (backward : order → maximum → Included B C → ExistsUnique A) :
    order → maximum → (ExistsUnique A ↔ Included B C) :=
  fun ho hm => ⟨forward ho hm, backward ho hm⟩
theorem star_230_54 (order : Prop) (maximum : Prop)
    (forward : order → maximum → Included A B → C x)
    (backward : order → maximum → C x → Included A B) :
    order → maximum → (Included A B ↔ C x) :=
  fun ho hm => ⟨forward ho hm, backward ho hm⟩

end PM.Architecture.Star230FinalKernel
