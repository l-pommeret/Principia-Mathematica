namespace PM.Architecture.Star35ClosingKernel
universe u
abbrev Class (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def lr (a : Class α) (R : Rel α) : Rel α := fun x y => a x ∧ R x y
def rr (R : Rel α) (b : Class α) : Rel α := fun x y => R x y ∧ b y
def br (a : Class α) (R : Rel α) (b : Class α) : Rel α := fun x y => a x ∧ R x y ∧ b y
def up (a b : Class α) : Rel α := fun x y => a x ∧ b y
def comp (R S : Rel α) : Rel α := fun x z => ∃ y, R x y ∧ S y z
def cnv (R : Rel α) : Rel α := fun x y => R y x
def dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def field (R : Rel α) : Class α := fun x => dom R x ∨ cod R x
def ri (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y
def ru (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def negR (R : Rel α) : Rel α := fun x y => ¬ R x y
def negC (a : Class α) : Class α := fun x => ¬ a x
def ci (a b : Class α) : Class α := fun x => a x ∧ b x
def nonemptyC (a : Class α) := ∃ x, a x
def nonemptyR (R : Rel α) := ∃ x y, R x y
def cinc (a b : Class α) := ∀ x, a x → b x
def rinc (R S : Rel α) := ∀ x y, R x y → S x y
def disj (a b : Class α) := ∀ x, ¬ (a x ∧ b x)

theorem star_35_7 (φ : Class α → Prop) (R : Rel α) (b : Class α) (y : α)
    (hφ : φ (fun x => R x y ∧ b y) ↔ b y ∧ φ (fun x => R x y)) :
    φ (fun x => rr R b x y) ↔ b y ∧ φ (fun x => R x y) := hφ
theorem star_35_71 (R S : Rel α) (b : Class α)
    (h : ∀ y, b y → (fun x => R x y) = fun x => S x y) : rr R b = rr S b := by
  funext x y; apply propext; constructor
  · rintro ⟨hR,hb⟩; exact ⟨congrFun (h y hb) x ▸ hR,hb⟩
  · rintro ⟨hS,hb⟩; exact ⟨congrFun (h y hb).symm x ▸ hS,hb⟩
theorem star_35_75 (a b : Class α) (R : Rel α) :
    lr (fun _ => False) R = (fun _ _ => False) ∧ rr R (fun _ => False) = (fun _ _ => False) ∧
    br (fun _ => False) R b = (fun _ _ => False) ∧ br a R (fun _ => False) = (fun _ _ => False) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext x y <;> apply propext <;> simp [lr,rr,br]
theorem star_35_76 (R : Rel α) : lr (fun _ => True) R = R ∧ rr R (fun _ => True) = R ∧
    br (fun _ => True) R (fun _ => True) = R := by
  refine ⟨?_, ?_, ?_⟩ <;> funext x y <;> apply propext <;> simp [lr,rr,br]
theorem star_35_81 (a : Class α) (x y : α) : lr a (fun _ _ => True) x y ↔ a x := by simp [lr]
theorem star_35_812 (b : Class α) (x y : α) : rr (fun _ _ => True) b x y ↔ b y := by simp [rr]
theorem star_35_82 (a b : Class α) : up a b = br a (fun _ _ => True) b := by
  funext x y; apply propext; simp [up,br]
theorem star_35_822 (a b : Class α) (R : Rel α) : br a R b = ri R (up a b) := by
  funext x y; apply propext; simp [br,ri,up,and_assoc,and_left_comm,and_comm]
theorem star_35_83 (R : Rel α) (a b : Class α) :
    (cinc (dom R) a ∧ cinc (cod R) b) ↔ rinc R (up a b) := by
  constructor
  · rintro ⟨ha,hb⟩ x y hR; exact ⟨ha x ⟨y,hR⟩,hb y ⟨x,hR⟩⟩
  · intro h; constructor
    · rintro x ⟨y,hR⟩; exact (h x y hR).1
    · rintro y ⟨x,hR⟩; exact (h x y hR).2
theorem star_35_831 (a b : Class α) : negR (up a b) =
    ru (ru (up (negC a) b) (up a (negC b))) (up (negC a) (negC b)) := by
  funext x y; apply propext; change (¬(a x ∧ b y)) ↔ ((¬a x ∧ b y) ∨ (a x ∧ ¬b y)) ∨ (¬a x ∧ ¬b y)
  classical
  by_cases ha : a x <;> by_cases hb : b y <;> simp [ha,hb]
theorem star_35_832 (a b : Class α) (R : Rel α) : negR (br a R b) =
    ru (ru (ru (up (negC a) b) (up a (negC b))) (up (negC a) (negC b))) (negR R) := by
  funext x y; apply propext
  change (¬(a x ∧ R x y ∧ b y)) ↔ (((¬a x ∧ b y) ∨ (a x ∧ ¬b y)) ∨ (¬a x ∧ ¬b y)) ∨ ¬R x y
  classical
  by_cases ha : a x <;> by_cases hb : b y <;> by_cases hR : R x y <;> simp [ha,hb,hR]
theorem star_35_834 (a b c d : Class α) : ri (up a b) (up c d) = up (ci a c) (ci b d) := by
  funext x y; apply propext; simp [ri,up,ci,and_assoc,and_left_comm,and_comm]
theorem star_35_84 (a b : Class α) : cnv (up a b) = up b a := by
  funext x y; apply propext; simp [cnv,up,and_comm]
theorem star_35_85 (a b : Class α) (h : nonemptyC b) : dom (up a b) = a := by
  rcases h with ⟨y,hy⟩; funext x; apply propext; constructor
  · rintro ⟨z,ha,hz⟩; exact ha
  · intro ha; exact ⟨y,ha,hy⟩
theorem star_35_86 (a b : Class α) (h : nonemptyC a) : cod (up a b) = b := by
  rcases h with ⟨x,hx⟩; funext y; apply propext; constructor
  · rintro ⟨z,hz,hb⟩; exact hb
  · intro hb; exact ⟨x,hx,hb⟩
theorem star_35_87 (a b : Class α) : nonemptyR (up a b) ↔ nonemptyC a ∧ nonemptyC b := by
  constructor
  · rintro ⟨x,y,ha,hb⟩; exact ⟨⟨x,ha⟩,⟨y,hb⟩⟩
  · rintro ⟨⟨x,ha⟩,⟨y,hb⟩⟩; exact ⟨x,y,ha,hb⟩
theorem star_35_88 (a b : Class α) : up a b = (fun _ _ => False) ↔
    a = (fun _ => False) ∨ b = (fun _ => False) := by
  classical
  constructor
  · intro h
    by_cases ha : ∃ x, a x
    · right; funext y; apply propext; constructor
      · intro hb; rcases ha with ⟨x,hx⟩; have : up a b x y := ⟨hx,hb⟩; simpa [h] using this
      · intro hf; exact hf.elim
    · left; funext x; apply propext; simp; exact fun hx => ha ⟨x,hx⟩
  · rintro (rfl | rfl) <;> funext x y <;> apply propext <;> simp [up]
theorem star_35_881 (R : Rel α) (a b : Class α) (h : cinc (cod R) a) :
    comp R (up a b) = up (dom R) b := by
  funext x z; apply propext; constructor
  · rintro ⟨y,hR,⟨ha,hb⟩⟩; exact ⟨⟨y,hR⟩,hb⟩
  · rintro ⟨⟨y,hR⟩,hb⟩; exact ⟨y,hR,⟨h y ⟨x,hR⟩,hb⟩⟩
theorem star_35_882 (R : Rel α) (a b : Class α) (h : cinc (dom R) b) :
    comp (up a b) R = up a (cod R) := by
  funext x z; apply propext; constructor
  · rintro ⟨y,⟨ha,hb⟩,hR⟩; exact ⟨ha,⟨y,hR⟩⟩
  · rintro ⟨ha,⟨y,hR⟩⟩; exact ⟨y,⟨ha,h y ⟨z,hR⟩⟩,hR⟩
theorem star_35_89 (a b c : Class α) :
    (nonemptyC b → comp (up a b) (up b c) = up a c) ∧
    (¬ nonemptyC b → comp (up a b) (up b c) = fun _ _ => False) := by
  constructor
  · rintro ⟨y,hy⟩; funext x z; apply propext; constructor
    · rintro ⟨w,⟨ha,hbw⟩,hbw',hc⟩; exact ⟨ha,hc⟩
    · rintro ⟨ha,hc⟩; exact ⟨y,⟨ha,hy⟩,hy,hc⟩
  · intro hn; funext x z; apply propext; constructor
    · rintro ⟨y,⟨ha,hy⟩,hy',hc⟩; exact hn ⟨y,hy⟩
    · intro hf; exact hf.elim
theorem star_35_891 (a b : Class α) (h : nonemptyC b ∨ ¬ nonemptyC a) :
    comp (up a b) (up b a) = up a a := by
  rcases h with hb | ha
  · exact (star_35_89 a b a).1 hb
  · have ea : a = fun _ => False := by funext x; apply propext; simp; exact fun hx => ha ⟨x,hx⟩
    subst a; funext x y; apply propext; simp [comp,up]
theorem star_35_892 (a : Class α) : comp (up a a) (up a a) = up a a := by
  classical
  by_cases h : nonemptyC a
  · exact (star_35_89 a a a).1 h
  · exact star_35_891 a a (Or.inr h)
theorem star_35_895 (a b : Class α) (h : disj a b) : comp (up a b) (up a b) = fun _ _ => False := by
  funext x z; apply propext; constructor
  · rintro ⟨y,⟨ha,hb⟩,hay,hbz⟩; exact h y ⟨hay,hb⟩
  · intro hf; exact hf.elim
theorem star_35_9 (a : Class α) : dom (up a a) = a ∧ cod (up a a) = a ∧ field (up a a) = a := by
  classical
  by_cases h : nonemptyC a
  · exact ⟨star_35_85 a a h, star_35_86 a a h, by
      funext x; apply propext; simp [field,star_35_85 a a h,star_35_86 a a h]⟩
  · have ea : a = fun _ => False := by funext x; apply propext; simp; exact fun hx => h ⟨x,hx⟩
    subst a
    refine ⟨?_, ?_, ?_⟩ <;> funext x <;> apply propext <;> simp [dom,cod,field,up]
theorem star_35_91 (R : Rel α) (a : Class α) : rinc R (up a a) ↔ cinc (field R) a := by
  constructor
  · intro h x hx; cases hx with
    | inl hd => rcases hd with ⟨y,hR⟩; exact (h x y hR).1
    | inr hc => rcases hc with ⟨y,hR⟩; exact (h y x hR).2
  · intro h x y hR; exact ⟨h x (Or.inl ⟨y,hR⟩),h y (Or.inr ⟨x,hR⟩)⟩
theorem star_35_92 (P R : Rel α) (a : Class α) (hP : P = up a a) :
    rinc R P ↔ cinc (field R) (field P) := by subst P; simpa [(star_35_9 a).2.2] using star_35_91 R a
theorem star_35_93 (φ : Class α → Prop) : (∀ R : Rel α, φ (dom R)) ↔ ∀ a : Class α, φ a := by
  constructor
  · intro h a; simpa [(star_35_9 a).1] using h (up a a)
  · intro h R; exact h (dom R)
theorem star_35_931 (φ : Class α → Prop) : (∀ R : Rel α, φ (cod R)) ↔ ∀ a : Class α, φ a := by
  constructor
  · intro h a; simpa [(star_35_9 a).2.1] using h (up a a)
  · intro h R; exact h (cod R)
theorem star_35_932 (φ : Class α → Prop) : (∀ R : Rel α, φ (field R)) ↔ ∀ a : Class α, φ a := by
  constructor
  · intro h a; simpa [(star_35_9 a).2.2] using h (up a a)
  · intro h R; exact h (field R)
theorem star_35_94 (φ : Class α → Prop) : (∃ R : Rel α, φ (dom R)) ↔ ∃ a : Class α, φ a := by
  constructor
  · rintro ⟨R,h⟩; exact ⟨dom R,h⟩
  · rintro ⟨a,h⟩
    have hd : dom (up a a) = a := (star_35_9 a).1
    exact ⟨up a a, hd.symm ▸ h⟩
theorem star_35_941 (φ : Class α → Prop) : (∃ R : Rel α, φ (cod R)) ↔ ∃ a : Class α, φ a := by
  constructor
  · rintro ⟨R,h⟩; exact ⟨cod R,h⟩
  · rintro ⟨a,h⟩
    have hc : cod (up a a) = a := (star_35_9 a).2.1
    exact ⟨up a a, hc.symm ▸ h⟩
theorem star_35_942 (φ : Class α → Prop) : (∃ R : Rel α, φ (field R)) ↔ ∃ a : Class α, φ a := by
  constructor
  · rintro ⟨R,h⟩; exact ⟨field R,h⟩
  · rintro ⟨a,h⟩
    have hf : field (up a a) = a := (star_35_9 a).2.2
    exact ⟨up a a, hf.symm ▸ h⟩
end PM.Architecture.Star35ClosingKernel
