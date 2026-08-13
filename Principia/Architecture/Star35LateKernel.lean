namespace PM.Architecture.Star35LateKernel
universe u v w
abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop
def lr (a : Class α) (R : Relation α β) : Relation α β := fun x y => a x ∧ R x y
def rr (R : Relation α β) (b : Class β) : Relation α β := fun x y => R x y ∧ b y
def br (a : Class α) (R : Relation α β) (b : Class β) : Relation α β := fun x y => a x ∧ R x y ∧ b y
def comp (R : Relation α β) (S : Relation β γ) : Relation α γ := fun x z => ∃ y, R x y ∧ S y z
def cnv (R : Relation α β) : Relation β α := fun y x => R x y
def dom (R : Relation α β) : Class α := fun x => ∃ y, R x y
def cod (R : Relation α β) : Class β := fun y => ∃ x, R x y
def ci (a b : Class α) : Class α := fun x => a x ∧ b x
def ru (R S : Relation α β) : Relation α β := fun x y => R x y ∨ S x y
def inc (a b : Class α) := ∀ x, a x → b x
def disj (a b : Class α) := ∀ x, ¬ (a x ∧ b x)

theorem star_35_471 (P : Relation α β) (a : Class β) (R : Relation β γ)
    (h : disj (cod P) a) : comp P (lr a R) = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y, hP, ha, hR⟩; exact h y ⟨⟨x,hP⟩,ha⟩
  · intro hf; exact hf.elim
theorem star_35_472 (R : Relation α β) (a : Class β) (P : Relation β γ)
    (h : disj (dom P) a) : comp (rr R a) P = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y, ⟨hR,ha⟩,hP⟩; exact h y ⟨⟨z,hP⟩,ha⟩
  · intro hf; exact hf.elim
theorem star_35_473 (P : Relation α β) (a : Class β) (R : Relation β γ) (c : Class γ)
    (h : disj (cod P) a) : comp P (br a R c) = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y,hP,ha,hR,hc⟩; exact h y ⟨⟨x,hP⟩,ha⟩
  · intro hf; exact hf.elim
theorem star_35_474 (a : Class α) (R : Relation α β) (b : Class β) (P : Relation β γ)
    (h : disj (dom P) b) : comp (br a R b) P = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y,⟨ha,hR,hb⟩,hP⟩; exact h y ⟨⟨z,hP⟩,hb⟩
  · intro hf; exact hf.elim
theorem star_35_48 (P : Relation α β) (a : Class β) (R : Relation β γ)
    (h : inc (cod P) a) : comp P (lr a R) = comp P R := by
  funext x z; apply propext; constructor
  · rintro ⟨y,hP,ha,hR⟩; exact ⟨y,hP,hR⟩
  · rintro ⟨y,hP,hR⟩; exact ⟨y,hP,h y ⟨x,hP⟩,hR⟩
theorem star_35_481 (P : Relation α β) (b : Class β) (R : Relation β γ)
    (h : inc (dom R) b) : comp (rr P b) R = comp P R := by
  funext x z; apply propext; constructor
  · rintro ⟨y,⟨hP,hb⟩,hR⟩; exact ⟨y,hP,hR⟩
  · rintro ⟨y,hP,hR⟩; exact ⟨y,⟨hP,h y ⟨z,hR⟩⟩,hR⟩
theorem star_35_51 (a : Class α) (R : Relation α β) : cnv (lr a R) = rr (cnv R) a := by
  funext y x; apply propext; simp [cnv,lr,rr,and_comm]
theorem star_35_52 (R : Relation α β) (b : Class β) : cnv (rr R b) = lr b (cnv R) := by
  funext y x; apply propext; simp [cnv,lr,rr,and_comm]
theorem star_35_53 (a : Class α) (R : Relation α β) (b : Class β) : cnv (br a R b) = br b (cnv R) a := by
  funext y x; apply propext; simp [cnv,br, and_assoc, and_left_comm, and_comm]
theorem star_35_61 (a : Class α) (R : Relation α β) : dom (lr a R) = ci a (dom R) := by
  funext x; apply propext; constructor
  · rintro ⟨y,ha,hR⟩; exact ⟨ha,⟨y,hR⟩⟩
  · rintro ⟨ha,y,hR⟩; exact ⟨y,ha,hR⟩
theorem star_35_62 (a : Class α) (R : Relation α β) (h : inc a (dom R)) : dom (lr a R) = a := by
  funext x; apply propext; constructor
  · rintro ⟨y,ha,hR⟩; exact ha
  · intro ha; rcases h x ha with ⟨y,hR⟩; exact ⟨y,ha,hR⟩
theorem star_35_63 (a : Class α) (R : Relation α β) : inc (dom R) a ↔ lr a R = R := by
  constructor
  · intro h; funext x y; apply propext; constructor
    · exact fun q => q.2
    · intro q; exact ⟨h x ⟨y,q⟩,q⟩
  · intro h x hx; rcases hx with ⟨y,hy⟩; have : lr a R x y := h.symm ▸ hy; exact this.1
theorem star_35_64 (R : Relation α β) (b : Class β) : cod (rr R b) = ci b (cod R) := by
  funext y; apply propext; constructor
  · rintro ⟨x,hR,hb⟩; exact ⟨hb,⟨x,hR⟩⟩
  · rintro ⟨hb,x,hR⟩; exact ⟨x,hR,hb⟩
theorem star_35_641 (a : Class α) (R : Relation α β) (h : disj a (dom R)) : lr a R = fun _ _ => False := by
  funext x y; apply propext; constructor
  · rintro ⟨ha,hR⟩; exact h x ⟨ha,⟨y,hR⟩⟩
  · intro hf; exact hf.elim
theorem star_35_642 (a : Class β) (R : Relation α β) (h : disj a (cod R)) : rr R a = fun _ _ => False := by
  funext x y; apply propext; constructor
  · rintro ⟨hR,ha⟩; exact h y ⟨ha,⟨x,hR⟩⟩
  · intro hf; exact hf.elim
theorem star_35_643 (a : Class α) (R S : Relation α β) (h : disj a (dom R)) : lr a (ru R S) = lr a S := by
  funext x y; apply propext; constructor
  · rintro ⟨ha,hR|hS⟩
    · exact (h x ⟨ha,⟨y,hR⟩⟩).elim
    · exact ⟨ha,hS⟩
  · rintro ⟨ha,hS⟩; exact ⟨ha,Or.inr hS⟩
theorem star_35_644 (a : Class β) (R S : Relation α β) (h : disj a (cod R)) : rr (ru R S) a = rr S a := by
  funext x y; apply propext; constructor
  · rintro ⟨hR|hS,ha⟩
    · exact (h y ⟨ha,⟨x,hR⟩⟩).elim
    · exact ⟨hS,ha⟩
  · rintro ⟨hS,ha⟩; exact ⟨Or.inr hS,ha⟩
theorem star_35_65 (R : Relation α β) (b : Class β) (h : inc b (cod R)) : cod (rr R b) = b := by
  funext y; apply propext; constructor
  · rintro ⟨x,hR,hb⟩; exact hb
  · intro hb; rcases h y hb with ⟨x,hR⟩; exact ⟨x,hR,hb⟩
theorem star_35_66 (R : Relation α β) (b : Class β) : inc (cod R) b ↔ rr R b = R := by
  constructor
  · intro h; funext x y; apply propext; constructor
    · exact fun q => q.1
    · intro q; exact ⟨q,h y ⟨x,q⟩⟩
  · intro h y hy; rcases hy with ⟨x,hx⟩; have : rr R b x y := h.symm ▸ hx; exact this.2
theorem star_35_671 (R : Relation α β) (S : Relation β γ) : dom (comp R S) = dom (rr R (dom S)) := by
  funext x; apply propext; constructor
  · rintro ⟨z,y,hR,hS⟩; exact ⟨y,hR,⟨z,hS⟩⟩
  · rintro ⟨y,hR,z,hS⟩; exact ⟨z,y,hR,hS⟩
theorem star_35_672 (R : Relation α β) (S : Relation β γ) : cod (comp R S) = cod (lr (cod R) S) := by
  funext z; apply propext; constructor
  · rintro ⟨x,y,hR,hS⟩; exact ⟨y,⟨x,hR⟩,hS⟩
  · rintro ⟨y,⟨x,hR⟩,hS⟩; exact ⟨x,y,hR,hS⟩
theorem star_35_68 (a b : Class α) (R : Relation α α) (h : disj a b) : comp (br a R b) (br a R b) = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y,⟨ha,hxy,hby⟩,hay,hyz,hbz⟩; exact h y ⟨hay,hby⟩
  · intro hf; exact hf.elim
end PM.Architecture.Star35LateKernel
