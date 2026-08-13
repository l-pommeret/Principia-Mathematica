namespace PM.Architecture.Star113OpeningKernel
universe u
abbrev Class (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def PairRel (x y : α) : Rel α := fun a b => a = x ∧ b = y
def Product (b a : Class α) : Class (Rel α) := fun R => ∃ x y, a x ∧ b y ∧ R = PairRel x y
def Empty (a : Class α) := ∀ x, ¬ a x
def Nonempty (a : Class α) := ∃ x, a x
def Converse (R : Rel α) : Rel α := fun x y => R y x
def converseSet (s : Class (Rel α)) : Class (Rel α) := fun R => s (Converse R)
def Included (a b : Class α) := ∀ x, a x → b x
def Swap (R : Rel α) : Rel α := Converse R

theorem star_113_1 (a b : Class α) : Product b a = fun R => ∃ x y, a x ∧ b y ∧ R = PairRel x y := rfl
theorem star_113_101 (R : Rel α) (a b : Class α) : Product b a R ↔ ∃ x y, a x ∧ b y ∧ R = PairRel x y := Iff.rfl
theorem star_113_102 (a b : Class α) (y : α) (hy : b y) :
    (fun R => ∃ x, a x ∧ R = PairRel x y) = fun R => ∃ x, a x ∧ R = PairRel x y := rfl
theorem star_113_104 (a : Class α) (y : α) : ∃ s : Class (Rel α), s = fun R => ∃ x, a x ∧ R = PairRel x y := ⟨_,rfl⟩
theorem star_113_105 (a : Class α) (ha : Nonempty a) :
    ∀ x y z, a x → a y → PairRel x z = PairRel y z → x = y := by
  intro x y z hx hy h
  have q : PairRel x z x z := ⟨rfl,rfl⟩
  have := congrFun (congrFun h x) z ▸ q
  exact this.1
theorem star_113_106 (a b : Class α) (x y : α) (hx : a x) (hy : b y) : Product b a (PairRel x y) := ⟨x,y,hx,hy,rfl⟩
theorem star_113_107 (a b : Class α) (ha : Nonempty a) (hb : Nonempty b) : Nonempty (Product b a) := by
  rcases ha with ⟨x,hx⟩; rcases hb with ⟨y,hy⟩; exact ⟨PairRel x y,star_113_106 a b x y hx hy⟩
theorem star_113_11 (a b : Class α) :
    (∀ y, b y → ∃ s : Class (Rel α), s = fun R => ∃ x, a x ∧ R = PairRel x y) := fun y hy => ⟨_,rfl⟩
theorem star_113_111 (a b : Class α) : ∃ s : Class (Rel α), s = Product b a := ⟨_,rfl⟩
theorem star_113_112 (a b : Class α) (ha : Empty a) : Product b a = fun _ => False := by
  funext R; apply propext; constructor
  · rintro ⟨x,y,hx,hy,e⟩; exact ha x hx
  · intro hf; exact hf.elim
theorem star_113_113 (a b : Class α) (hb : Empty b) : Product b a = fun _ => False := by
  funext R; apply propext; constructor
  · rintro ⟨x,y,hx,hy,e⟩; exact hb y hy
  · intro hf; exact hf.elim
theorem star_113_114 (a b : Class α) :
    (Empty a ∨ Empty b) ↔ Empty (Product b a) := by
  constructor
  · rintro (ha|hb)
    · intro R; rw [star_113_112 a b ha]; simp
    · intro R; rw [star_113_113 a b hb]; simp
  · intro h
    classical
    by_cases ha : Empty a
    · exact Or.inl ha
    · right; intro y hy; apply ha; intro x hx; exact h (PairRel x y) ⟨x,y,hx,hy,rfl⟩
theorem star_113_115 (a b : Class α) : converseSet (Product b a) = Product a b := by
  funext R; apply propext; constructor
  · rintro ⟨x,y,hx,hy,e⟩; exact ⟨y,x,hy,hx,by
      funext p q; apply propext
      have ep := congrFun (congrFun e q) p
      simpa [Converse,PairRel,and_comm] using ep⟩
  · rintro ⟨y,x,hy,hx,e⟩; exact ⟨x,y,hx,hy,by subst R; funext p q; apply propext; simp [Converse,PairRel,and_comm]⟩
theorem star_113_117 (a b : Class α) : converseSet (converseSet (Product b a)) = Product b a := by rw [star_113_115,star_113_115]
theorem star_113_118 (a b : Class α) :
    (∀ R, Product b a R → ∃ x, a x) ∧ (∀ R, Product b a R → ∃ y, b y) := by
  constructor <;> rintro R ⟨x,y,hx,hy,e⟩
  · exact ⟨x,hx⟩
  · exact ⟨y,hy⟩
theorem star_113_12 (a b : Class α) : ∃ s : Class (Rel α), s = Product b a := ⟨_,rfl⟩

end PM.Architecture.Star113OpeningKernel
