import Principia.Architecture.Star212LimitsKernel
namespace PM.Architecture.Star212ExistenceKernel
open PM.Architecture.Star212OpeningKernel PM.Architecture.Star212MiddleKernel PM.Architecture.Star212OrderKernel PM.Architecture.Star212LimitsKernel
universe u
def HasSuccessor (R : Rel α) (c : Class α) := ∃ x, c x ∧ ∀ y, c y → y = x ∨ R x y
theorem star_212_54 (c : Class (Class α)) : ∀ a b, Sgm c a b → c a ∧ c b := fun _ _ h => ⟨h.1,h.2.1⟩
theorem star_212_55 (c : Class (Class α)) (a : Class α) : Dom (Sgm c) a → ∃ b, Sgm c a b := fun h => h
theorem star_212_6 (R : Rel α) (c : Class α) : HasGreatest R c → ∃ x, Greatest R c x := fun h => h
theorem star_212_601 (R : Rel α) (c : Class α) : HasGreatest R c ↔ ∃ x, Greatest R c x := Iff.rfl
theorem star_212_602 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : HasGreatest R c := ⟨x,h⟩
theorem star_212_61 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : c x := h.1
theorem star_212_62 (R : Rel α) (c : Class α) : HasLeast R c ↔ ∃ x, Least R c x := Iff.rfl
theorem star_212_621 (R : Rel α) (c : Class α) : HasSuccessor R c ↔ ∃ x, c x ∧ ∀ y, c y → y = x ∨ R x y := Iff.rfl
theorem star_212_63 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : HasSuccessor R c := ⟨x,h⟩
theorem star_212_631 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : c x := h.1
theorem star_212_632 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : HasLeast R c := ⟨x,h⟩
theorem star_212_633 (R : Rel α) (c : Class α) (h : HasLeast R c) : ∃ x, c x := by rcases h with ⟨x,hx⟩; exact ⟨x,hx.1⟩
theorem star_212_65 (R : Rel α) (c : Class α) : HasSuccessor R c → ∃ x, c x := by rintro ⟨x,h,_⟩; exact ⟨x,h⟩
theorem star_212_651 (R : Rel α) (c : Class α) : HasSuccessor R c ∨ HasGreatest R c → (∃ x, c x) := by
  rintro (h | h)
  · exact star_212_65 R c h
  · rcases h with ⟨x,hx⟩; exact ⟨x,hx.1⟩
theorem star_212_652 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : HasGreatest R c := ⟨x,h⟩
end PM.Architecture.Star212ExistenceKernel
