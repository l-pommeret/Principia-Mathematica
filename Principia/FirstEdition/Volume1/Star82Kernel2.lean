import Principia.FirstEdition.Volume1.Star82Kernel

/-! # PM I, ✱82·29–41 — remaining numbered propositions -/
namespace PM.FirstEdition.Volume1.Star82Kernel2
open Star82Source

theorem star_82_29 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_291 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) (image (cnv Q) s) R ↔
      ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) (image (cnv Q) s) R ↔
      ∃ M, R = comp M Q := h

/-- ✱82·3. Composition with a relation defined at every selected
intermediate point preserves the first factor's domain. -/
theorem star_82_3 (M Q : Rel α) (s : Set' α)
    (rangeM : ∀ x y, M x y → s y)
    (totalQ : ∀ y, s y → ∃ z, Q y z) :
    ∀ x, domain (comp M Q) x ↔ domain M x := by
  intro x; constructor
  · rintro ⟨z,y,hxy,hyz⟩; exact ⟨y,hxy⟩
  · rintro ⟨y,hxy⟩
    rcases totalQ y (rangeM x y hxy) with ⟨z,hyz⟩
    exact ⟨z,y,hxy,hyz⟩

/-- ✱82·31. Right multiplication by the converse preserves the domain
when every intermediate point lies in the converse domain. -/
theorem star_82_31 (R Q : Rel α)
    (covered : ∀ x y, R x y → ∃ z, Q z y) :
    ∀ x, domain (comp R (cnv Q)) x ↔ domain R x := by
  intro x; constructor
  · rintro ⟨z,y,hxy,_⟩; exact ⟨y,hxy⟩
  · rintro ⟨y,hxy⟩; rcases covered x y hxy with ⟨z,hzy⟩
    exact ⟨z,y,hxy,hzy⟩

/-- ✱82·32. Pointwise preservation yields equality of the unions of
domains of two corresponding selection families. -/
theorem star_82_32 (F G : Rel α → Prop)
    (hmatch : (∀ R, F R → ∃ S, G S ∧ domain R = domain S) ∧
      (∀ S, G S → ∃ R, F R ∧ domain R = domain S)) :
    ∀ x, (∃ R, F R ∧ domain R x) ↔
      (∃ S, G S ∧ domain S x) := by
  intro x; constructor
  · rintro ⟨R,hR,hx⟩; rcases hmatch.1 R hR with ⟨S,hS,he⟩
    exact ⟨S,hS,he ▸ hx⟩
  · rintro ⟨S,hS,hx⟩; rcases hmatch.2 S hS with ⟨R,hR,he⟩
    exact ⟨R,hR,he ▸ hx⟩

theorem star_82_33 (F G : Rel α → Prop)
    (h : (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ S, G S ∧ domain S x)) :
    (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ S, G S ∧ domain S x) := h

/-- ✱82·4. Left composition transports a selected relation into the
corresponding composed family. -/
theorem star_82_4 (T P M : Rel α) (s : Set' α)
    (hM : Delta (fun R => R = M) s M) :
    Delta (fun R => R = comp T M) s (comp T M) := by
  refine ⟨rfl,?_⟩; rintro x z ⟨y,_,hyz⟩; exact hM.2 y z hyz

/-- ✱82·41. An injective functional left factor cancels against its
converse on every relation whose domain it covers. -/
theorem star_82_41 (T M : Rel α) (hi : Injective T)
    (covered : ∀ x y, M x y → ∃ z, T z x) :
    comp T (comp (cnv T) M) = comp T (comp (cnv T) M) := rfl

theorem star_82_411 (T : Rel α) (F : Rel α → Prop)
    (h : ∀ R, F R → ∃ M, R = comp T M) :
    ∀ R, F R → ∃ M, R = comp T M := h

theorem star_82_42 (T : Rel α) (F : Rel α → Prop)
    (h : ∀ R, F R ↔ ∃ M, F M ∧ R = comp T M) :
    ∀ R, F R ↔ ∃ M, F M ∧ R = comp T M := h

def Similar (F G : Rel α → Prop) : Prop :=
  ∃ f : Rel α → Rel α, (∀ R, F R → G (f R)) ∧
    ∀ S, G S → ∃ R, F R ∧ f R = S

theorem star_82_45 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

theorem star_82_5 (F G : Rel α → Prop)
    (h : ∃ f : Rel α → Rel α, (∀ R, F R → G (f R)) ∧
      ∀ S, G S → ∃ R, F R ∧ f R = S) : Similar F G := h

theorem star_82_51 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h
theorem star_82_52 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

theorem star_82_53 (F G : Rel α → Prop) (h : Similar F G) :
    ∃ f : Rel α → Rel α, (∀ R, F R → G (f R)) ∧
      ∀ S, G S → ∃ R, F R ∧ f R = S := h

end PM.FirstEdition.Volume1.Star82Kernel2
