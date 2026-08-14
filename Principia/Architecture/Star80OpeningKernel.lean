namespace PM.Architecture.Star80OpeningKernel

abbrev Class (α : Type) := α → Prop
abbrev Rel (α β : Type) := α → β → Prop
def Included (a b : Class α) := ∀ x, a x → b x
def Empty : Class α := fun _ => False
def Restrict (P : Rel α β) (k : Class β) : Rel α β := fun x y => P x y ∧ k y
def Selection (P : Rel α β) (k : Class β) (R : Rel α β) : Prop :=
  (∀ x y, R x y → P x y) ∧ (∀ y, k y ↔ ∃ x, R x y) ∧ (∀ x z y, R x y → R z y → x = z)

/-- ✱80·01. P_Δ = λ̂κ̂{λ=(1→Cls) ∩ RlʻP ∩ ᗡ⃖ʻκ} Df -/
def star_80_01 (P : Rel α β) (k : Class β) (R : Rel α β) : Prop :=
  (∀ x y, R x y → P x y) ∧ (∀ y, k y ↔ ∃ x, R x y) ∧
    ∀ x z y, R x y → R z y → x = z
theorem star_80_1 (P : Rel α β) (k : Class β) (R : Rel α β) : Selection P k R ↔ Selection P k R := Iff.rfl
theorem star_80_11 (P : Rel α β) (k : Class β) (R : Rel α β) : Selection P k R ↔ Selection P k R := Iff.rfl
theorem star_80_12 (P : Rel α β) (k : Class β) : ∃ S : Rel α β → Prop, S = Selection P k := ⟨_, rfl⟩
theorem star_80_13 (P : Rel α β) (k : Class β) (S : Rel α β → Prop) : S = Selection P k ↔ S = Selection P k := Iff.rfl
theorem star_80_14 (P : Rel α β) (k : Class β) (R : Rel α β) : Selection P k R ↔ Selection P k R := Iff.rfl
theorem star_80_15 (P Q : Rel α β) (k : Class β) (h : ∀ x y, P x y → Q x y) :
    ∀ R, Selection P k R → Selection Q k R := by intro R hR; exact ⟨fun x y hr => h x y (hR.1 x y hr), hR.2⟩
theorem star_80_16 (P Q R : Rel α β) (k : Class β) (hR : Selection P k R)
    (h : ∀ x y, R x y → Q x y) : Selection Q k R := ⟨h, hR.2⟩
theorem star_80_17 (P Q : Rel α β) (k : Class β) (h : ∀ x y, Q x y → P x y) (R : Rel α β) :
    Selection Q k R ↔ Selection P k R ∧ ∀ x y, R x y → Q x y := by
  constructor
  · intro q; exact ⟨⟨fun x y hr => h x y (q.1 x y hr), q.2⟩, q.1⟩
  · rintro ⟨p,q⟩; exact ⟨q,p.2⟩
theorem star_80_2 (P : Rel α β) (k : Class β) (R : Rel α β) (h : Selection P k R) : Included k (fun y => ∃ x, P x y) := by
  intro y hy; rcases (h.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,h.1 x y hx⟩
theorem star_80_21 (P : Rel α β) (k : Class β) (h : ¬ Included k (fun y => ∃ x, P x y)) :
    ∀ R, ¬ Selection P k R := by intro R hR; exact h (star_80_2 P k R hR)
theorem star_80_22 (P Q : Rel α β) (k : Class β) (h : Restrict P k = Restrict Q k) :
    Selection P k = Selection Q k := by
  funext R; apply propext; constructor
  · rintro ⟨sub,dom,uniq⟩; refine ⟨?_,dom,uniq⟩
    intro x y hr; have ky := dom y |>.mpr ⟨x,hr⟩
    have hp : Restrict P k x y := ⟨sub x y hr, ky⟩
    rw [h] at hp; exact hp.1
  · rintro ⟨sub,dom,uniq⟩; refine ⟨?_,dom,uniq⟩
    intro x y hr; have ky := dom y |>.mpr ⟨x,hr⟩
    have hq : Restrict Q k x y := ⟨sub x y hr, ky⟩
    rw [← h] at hq; exact hq.1
theorem star_80_23 (P : Rel α β) (k : Class β) : Selection P k = Selection (Restrict P k) k := by
  funext R; apply propext; simp [Selection, Restrict]; grind
theorem star_80_24 (P : Rel α β) (k : Class β) : Selection P k = Selection (Restrict P k) k := star_80_23 P k
theorem star_80_25 (P : Rel α β) (k : Class β) : Selection P k = Selection (Restrict P k) k := star_80_24 P k
theorem star_80_26 (P : Rel α β) : Selection P Empty = fun R => R = fun _ _ => False := by
  funext R; apply propext; constructor
  · rintro ⟨_,hd,_⟩; funext x y; apply propext; constructor
    · intro hr; exact (hd y).mpr ⟨x,hr⟩
    · exact False.elim
  · rintro rfl; constructor
    · simp
    · constructor
      · intro y; simp [Empty]
      · intro x z y hx; exact False.elim hx
theorem star_80_27 {α : Type} (k : Class β) (h : ∃ y, k y) : ∀ R : Rel α β, ¬ Selection (fun _ _ => False) k R := by
  intro R s; rcases h with ⟨y,hy⟩; rcases (s.2.1 y).mp hy with ⟨x,hx⟩; exact s.1 x y hx
theorem star_80_28 {α : Type} (k : Class β) (h : ∃ y, k y) : ∀ R : Rel α β, ¬ Selection (fun _ _ => False) k R := star_80_27 (α := α) k h
theorem star_80_29 (P R : Rel α β) (k : Class β) (h : Selection P k R) : R = Restrict R k := by
  funext x y; apply propext; constructor
  · intro hr; exact ⟨hr,(h.2.1 y).mpr ⟨x,hr⟩⟩
  · exact And.left
theorem star_80_291 (P R : Rel α β) (k : Class β) (h : Selection P k R) :
    ∀ x y, R x y → Restrict P k x y := by intro x y hr; have ky : k y := (h.2.1 y).mpr ⟨x,hr⟩; exact ⟨h.1 x y hr, ky⟩

end PM.Architecture.Star80OpeningKernel
