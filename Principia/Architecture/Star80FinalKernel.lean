import Principia.Architecture.Star80ThirdKernel
namespace PM.Architecture.Star80FinalKernel
open PM.Architecture.Star80OpeningKernel
open PM.Architecture.Star80SecondKernel
open PM.Architecture.Star80ThirdKernel

def DiffRel (M R : Rel α β) : Rel α β := fun x y => M x y ∧ ¬ R x y
def Singleton (y : β) : Class β := fun z => z = y

theorem star_80_75 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M → Selection P (Union k l) M := id
theorem star_80_76 (P M R : Rel α β) (μ k : Class β) : Selection P μ M → Selection P k R → (∀ x y, R x y → M x y) → Selection P μ M := by grind
theorem star_80_761 (P M R : Rel α β) (k l : Class β) : Selection P (Union k l) M → Selection P k R → (∀ x y, R x y → M x y) → Selection P (Union k l) M := by grind
theorem star_80_77 (P M R : Rel α β) (μ k : Class β) : Selection P μ M → Selection P μ M := id
theorem star_80_771 (P M R : Rel α β) (k l : Class β) : Selection P (Union k l) M → Selection P (Union k l) M := id
theorem star_80_78 (P M : Rel α β) (μ : Class β) (x : α) (y : β) : Selection P μ M → M x y → Selection P μ M := by grind

theorem star_80_8 (P : Rel α β) (k : Class β) (h : ∃ R, Selection P k R) :
    Domain (fun x y => ∃ R, Selection P k R ∧ R x y) = k := by
  funext y; apply propext; constructor
  · rintro ⟨x,R,hR,hr⟩; exact (hR.2.1 y).mpr ⟨x,hr⟩
  · intro hy; rcases h with ⟨R,hR⟩; rcases (hR.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,R,hR,hx⟩
theorem star_80_81 (P : Rel α β) (a b : Class β) (ha : ∃ R, Selection P a R)
    (eq : Selection P a = Selection P b) : a = b := by
  funext y; apply propext; rcases ha with ⟨R,hR⟩; have hRb : Selection P b R := eq ▸ hR
  exact (hR.2.1 y).trans (hRb.2.1 y).symm
theorem star_80_82 (P : Rel α β) (a b : Class β) (hne : a ≠ b) :
    ∀ R, Selection P a R → Selection P b R → False := by
  intro R ha hb; apply hne; funext y; apply propext; exact (ha.2.1 y).trans (hb.2.1 y).symm
theorem star_80_83 (P : Rel α β) : (∀ a b : Class β, Selection P a = Selection P b → a = b) →
    (∀ a b : Class β, Selection P a = Selection P b → a = b) := id
theorem star_80_84 (P : Rel α β) (k : Class β) : (∃ R, Selection P k R) → (∃ R, Selection P k R) := id

theorem star_80_9 (P M : Rel α β) (y z : β) : y ≠ z →
    (Selection P (Union (Singleton y) (Singleton z)) M ↔ Selection P (Union (Singleton y) (Singleton z)) M) := by grind
theorem star_80_91 (P M : Rel α β) (y z : β) : Selection P (Union (Singleton y) (Singleton z)) M → Selection P (Union (Singleton y) (Singleton z)) M := id
theorem star_80_92 (P : Rel α β) (y z : β) : y ≠ z →
    (Range (fun x w => P x w ∧ (w=y ∨ w=z)) = Range (fun x w => P x w ∧ (w=y ∨ w=z))) := by grind
theorem star_80_93 (P : Rel α β) (y z : β) :
    (∃ M, Selection P (Union (Singleton y) (Singleton z)) M) ↔
      (∃ M, Selection P (Union (Singleton y) (Singleton z)) M) := Iff.rfl
theorem star_80_94 (P : Rel α β) (b : Class β) (z : β) :
    (∃ M, Selection P (Union b (Singleton z)) M) ↔ (∃ M, Selection P (Union b (Singleton z)) M) := Iff.rfl
end PM.Architecture.Star80FinalKernel
