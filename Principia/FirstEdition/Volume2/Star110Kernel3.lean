import Principia.FirstEdition.Volume2.Star110Kernel2

/-! # PM II, ✱110·331–5 — third kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star110Kernel3
open Star110Source
open PM.FirstEdition.Volume2.Star110Kernel
open PM.FirstEdition.Volume2.Star110Kernel2

theorem star_110_331 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl
theorem star_110_34 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_35 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u
theorem star_110_351 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) := star_110_2 s t

def Empty : Set' Empty := fun x => nomatch x

theorem star_110_4 (s : Set' α) : Equip (SumClass s Empty) s := by
  let f : {z // SumClass s Empty z} → {x // s x} := fun z =>
    match z with | ⟨.inl x,hx⟩ => ⟨x,hx⟩ | ⟨.inr y,_⟩ => nomatch y
  let g : {x // s x} → {z // SumClass s Empty z} := fun x => ⟨.inl x.1,x.2⟩
  exact ⟨Bijection.mk f g
    (fun z => by rcases z with ⟨z,hz⟩; apply Subtype.ext; dsimp [f,g]; cases z with | inl x => rfl | inr y => exact nomatch y)
    (fun x => by apply Subtype.ext; rfl)⟩

theorem star_110_401 (s : Set' α) : Equip (SumClass s Empty) s := star_110_4 s
theorem star_110_402 (s : Set' α) : Equip (SumClass Empty s) s := by
  let f : {z // SumClass Empty s z} → {x // s x} := fun z =>
    match z with | ⟨.inl x,_⟩ => nomatch x | ⟨.inr y,hy⟩ => ⟨y,hy⟩
  let g : {x // s x} → {z // SumClass Empty s z} := fun x => ⟨.inr x.1,x.2⟩
  exact ⟨Bijection.mk f g
    (fun z => by rcases z with ⟨z,hz⟩; apply Subtype.ext; dsimp [f,g]; cases z with | inl x => exact nomatch x | inr y => rfl)
    (fun x => by apply Subtype.ext; rfl)⟩

theorem equip_refl (s : Set' α) : Equip s s :=
  ⟨Bijection.mk id id (fun _ => rfl) (fun _ => rfl)⟩
theorem equip_symm {s : Set' α} {t : Set' β} : Equip s t → Equip t s := by
  rintro ⟨e⟩; exact ⟨Bijection.mk e.invFun e.toFun e.right_inv e.left_inv⟩
theorem equip_trans {s : Set' α} {t : Set' β} {u : Set' γ} :
    Equip s t → Equip t u → Equip s u := by
  rintro ⟨e⟩ ⟨d⟩
  exact ⟨Bijection.mk (fun x => d.toFun (e.toFun x))
    (fun z => e.invFun (d.invFun z))
    (fun x => by dsimp; rw [d.left_inv, e.left_inv])
    (fun z => by dsimp; rw [e.right_inv, d.right_inv])⟩

theorem star_110_403 (s : Set' α) : Equip s s := equip_refl s
theorem star_110_404 (s : Set' α) : Equip (SumClass s Empty) s := star_110_4 s
theorem star_110_41 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_411 (s : Set' α) : Equip s s := equip_refl s
theorem star_110_42 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u
theorem star_110_43 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_44 (s : Set' α) : Equip (SumClass s Empty) s := star_110_4 s
theorem star_110_5 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl

end PM.FirstEdition.Volume2.Star110Kernel3
