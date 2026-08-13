namespace PM.Architecture.Star60Kernel

abbrev Class (α : Sort u) := α → Prop
def Included (a b : Class α) := ∀ x, a x → b x
def Empty : Class α := fun _ => False
def Singleton (x : α) : Class α := fun y => y = x
def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Proper (a : Class α) := ∃ x, a x
def Cl (a : Class α) : Class (Class α) := fun b => Included b a
def ClEx (a : Class α) : Class (Class α) := fun b => Included b a ∧ Proper b
def Sum (k : Class (Class α)) : Class α := fun x => ∃ a, k a ∧ a x
def Product (k : Class (Class α)) : Class α := fun x => ∀ a, k a → a x

private theorem ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by funext x; exact propext (h x)

theorem star_60_1 (k : Class (Class α)) (a : Class α) : (k = Cl a) ↔ k = fun b => Included b a := Iff.rfl
theorem star_60_11 (k : Class (Class α)) (a : Class α) : (k = ClEx a) ↔ k = fun b => Included b a ∧ Proper b := Iff.rfl
theorem star_60_12 (a : Class α) : Cl a = fun b => Included b a := rfl
theorem star_60_13 (a : Class α) : ClEx a = fun b => Included b a ∧ Proper b := rfl
theorem star_60_14 (a : Class α) : ∃ k, k = Cl a := ⟨_, rfl⟩
theorem star_60_15 (a : Class α) : ∃ k, k = ClEx a := ⟨_, rfl⟩
theorem star_60_2 (a b : Class α) : Cl a b ↔ Included b a := Iff.rfl
theorem star_60_21 (a b : Class α) : ClEx a b ↔ Included b a ∧ Proper b := Iff.rfl
theorem star_60_22 (a b : Class α) : ClEx a b ↔ Cl a b ∧ Proper b := Iff.rfl
theorem star_60_23 (a b : Class α) : ClEx a b ↔ Cl a b ∧ b ≠ Empty := by
  constructor
  · rintro ⟨h, x, hx⟩; exact ⟨h, fun he => by rw [he] at hx; exact hx⟩
  · rintro ⟨h, hn⟩; refine ⟨h, ?_⟩
    cases Classical.em (∃ x, b x) with
    | inl hp => exact hp
    | inr hp => exact False.elim (hn (by apply ext; intro x; exact ⟨fun hx => hp ⟨x,hx⟩, False.elim⟩))
theorem star_60_24 (a : Class α) : ClEx a = fun b => Cl a b ∧ b ≠ Empty := by funext b; exact propext (star_60_23 a b)
theorem star_60_3 (a : Class α) : Cl a Empty := fun _ h => h.elim
theorem star_60_31 (a : Class α) : Proper (Cl a) := ⟨Empty, star_60_3 a⟩
theorem star_60_32 : Cl (Empty : Class α) = Singleton Empty := by
  apply ext; intro a; constructor
  · intro h; apply ext; intro x; exact ⟨fun hx => h x hx, False.elim⟩
  · intro h; cases h; exact fun _ z => z.elim
theorem star_60_34 (a : Class α) : Cl a a := fun _ h => h
theorem star_60_35 (a : Class α) : Proper a → ClEx a a := fun h => ⟨star_60_34 a, h⟩
theorem star_60_37 (x : α) : ClEx (Singleton x) = Singleton (Singleton x) := by
  apply ext; intro a; constructor
  · rintro ⟨ha, y, hy⟩; apply ext; intro z
    have hyx : y = x := ha y hy
    exact ⟨fun hz => ha z hz, fun hz => by subst z; subst y; exact hy⟩
  · intro h; cases h; exact ⟨fun _ hz => hz, x, rfl⟩
theorem star_60_391 (a b c : Class α) : Cl a b → Included c b → Cl a c := fun hab hcb x hx => hab x (hcb x hx)
theorem star_60_4 (a b c : Class α) : Cl a b → Cl a (Inter b c) := fun h x hx => h x hx.1
theorem star_60_41 (a b c : Class α) : Cl a b → Included c b → Proper c → ClEx a c := fun h hc hp => ⟨star_60_391 a b c h hc, hp⟩
theorem star_60_42 (a b c : Class α) : (Cl a b ∧ Cl a c) ↔ Cl a (Union b c) := by
  exact ⟨fun h x hx => hx.elim (h.1 x) (h.2 x), fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩⟩
theorem star_60_43 (a b c : Class α) : Cl a b → ClEx a c → ClEx a (Union b c) := by
  rintro hb ⟨hc, x, hx⟩; exact ⟨(star_60_42 a b c).mp ⟨hb,hc⟩, x, Or.inr hx⟩
theorem star_60_44 (a b r : Class α) : Cl (Union a b) r ↔ ∃ c d, Cl a c ∧ Cl b d ∧ r = Union c d := by
  constructor
  · intro h; refine ⟨Inter r a, Inter r b, ?_, ?_, ?_⟩
    · intro x hx; exact hx.2
    · intro x hx; exact hx.2
    · apply ext; intro x; constructor
      · intro hx; cases h x hx with | inl ha => exact Or.inl ⟨hx,ha⟩ | inr hb => exact Or.inr ⟨hx,hb⟩
      · intro hx; exact hx.elim And.left And.left
  · rintro ⟨c,d,hc,hd,rfl⟩; exact (star_60_42 (Union a b) c d).mp ⟨fun x hx => Or.inl (hc x hx), fun x hx => Or.inr (hd x hx)⟩
theorem star_60_45 (a : Class α) : Sum (Cl a) = a := by apply ext; intro x; exact ⟨fun h => h.choose_spec.1 x h.choose_spec.2, fun hx => ⟨Singleton x, fun y hy => hy ▸ hx, rfl⟩⟩
theorem star_60_5 (a : Class α) : Sum (ClEx a) = a := by apply ext; intro x; exact ⟨fun h => h.choose_spec.1.1 x h.choose_spec.2, fun hx => ⟨Singleton x, ⟨fun y hy => hy ▸ hx, x, rfl⟩, rfl⟩⟩
theorem star_60_501 (a : Class α) : Product (Cl a) = Empty := by apply ext; intro x; exact ⟨fun h => h Empty (star_60_3 a), False.elim⟩
theorem star_60_51 (k : Class (Class α)) (b : Class α) : Included (Sum k) b ↔ Included k (Cl b) := by
  exact ⟨fun h a ha x hx => h x ⟨a,ha,hx⟩, fun h x hx => h hx.choose hx.choose_spec.1 x hx.choose_spec.2⟩
theorem star_60_54 (a b : Class α) : Cl a = Cl b ↔ a = b := by exact ⟨fun h => by have := congrFun h a; exact ext (fun x => ⟨fun hx => (this.mp (star_60_34 a)) x hx, fun hx => ((congrFun h b).mpr (star_60_34 b)) x hx⟩), congrArg Cl⟩
theorem star_60_56 (k : Class (Class α)) : Included k (Cl (Sum k)) := fun a ha x hx => ⟨a,ha,hx⟩
theorem star_60_57 (a : Class α) (x : α) : a x → ClEx a (Singleton x) := fun hx => ⟨fun y hy => hy ▸ hx, x, rfl⟩
theorem star_60_6 (a : Class α) (x y : α) : a x → a y → ClEx a (Union (Singleton x) (Singleton y)) := by
  intro hx hy; exact ⟨fun z hz => hz.elim (fun e => e ▸ hx) (fun e => e ▸ hy), x, Or.inl rfl⟩

end PM.Architecture.Star60Kernel
