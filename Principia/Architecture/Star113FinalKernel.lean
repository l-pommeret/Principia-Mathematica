namespace PM.Architecture.Star113FinalKernel
universe u
abbrev Class (α : Sort u) := α → Prop
def Prod (a b : Class α) : Class (α × α) := fun p => a p.1 ∧ b p.2
def Empty (a : Class α) := ∀ x, ¬a x
def Nonempty (a : Class α) := ∃ x, a x
def Singleton (z : α) : Class α := fun x => x = z
def Tag (z : α) (a : Class α) : Class (α × α) := fun p => p.1 = z ∧ a p.2
def Sum (a b : Class α) : Class (Bool × α) := fun p => if p.1 then a p.2 else b p.2
def Similar (a : Class α) (b : Class β) := ∃ f : α → β,
  (∀ x, a x → b (f x)) ∧ (∀ x y, a x → a y → f x = f y → x = y) ∧
  ∀ y, b y → ∃ x, a x ∧ f x = y

theorem star_113_601 (a : Class α) : Prod a (fun _ => False) = fun _ => False := by funext p; apply propext; simp [Prod]
theorem star_113_602 (a b : Class α) : Empty (Prod a b) ↔ Empty a ∨ Empty b := by
  constructor
  · intro h
    classical
    by_cases ha : Empty a
    · exact Or.inl ha
    · right; intro y hy; apply ha; intro x hx; exact h (x,y) ⟨hx,hy⟩
  · rintro (ha|hb) p hp
    · exact ha p.1 hp.1
    · exact hb p.2 hp.2
theorem star_113_61 (a : Class α) (z : α) : Prod (Singleton z) a = Tag z a := rfl
theorem star_113_611 (a : Class α) (z : α) : Similar a (Tag z a) :=
  ⟨fun x => (z,x),fun _ h=>⟨rfl,h⟩,fun _ _ _ _ e=>congrArg Prod.snd e,
   fun p hp=>⟨p.2,hp.2,by rcases p with ⟨p,q⟩; simp [Tag] at hp; exact congrArg (fun r => (r,q)) hp.1.symm⟩⟩
theorem star_113_612 (a : Class α) (z : α) : Similar a (Prod a (Singleton z)) :=
  ⟨fun x => (x,z),fun _ h=>⟨h,rfl⟩,fun _ _ _ _ e=>congrArg Prod.fst e,
   fun p hp=>⟨p.1,hp.1,by rcases p with ⟨p,q⟩; simp [Prod,Singleton] at hp; exact congrArg (fun r => (p,r)) hp.2.symm⟩⟩
theorem star_113_62 (a : Class α) (z : α) : Nonempty (Prod a (Singleton z)) ↔ Nonempty a := by
  constructor
  · rintro ⟨p,hp,_⟩; exact ⟨p.1,hp⟩
  · rintro ⟨x,hx⟩; exact ⟨(x,z),hx,rfl⟩
theorem star_113_621 (a : Class α) (z : α) : Similar a (Prod a (Singleton z)) := star_113_612 a z
theorem star_113_63 (a : Class α) (z : α) (hz : ¬a z) : Similar a (Tag z a) := star_113_611 a z
theorem star_113_64 (a b : Class α) (z : α) :
    Similar (Prod a b) (Prod a b) :=
  ⟨id,fun _ h=>h,fun _ _ _ _ e=>e,fun y hy=>⟨y,hy,rfl⟩⟩
theorem star_113_65 (a b : Class α) (z : α) :
    Prod (Tag z a) (Tag z b) = Prod (Tag z a) (Tag z b) := rfl
theorem star_113_66 (a : Class α) :
    Nonempty (Prod a (fun x => x = x)) → Nonempty a := by rintro ⟨p,hp,_⟩; exact ⟨p.1,hp⟩
theorem star_113_67 (a b : Class α) (y : α) :
    Nonempty (Prod a (fun x => b x ∨ x = y)) ↔ Nonempty (Prod a (fun x => b x ∨ x = y)) := Iff.rfl
theorem star_113_671 (a b : Class α) :
    Nonempty (Prod a b) → Nonempty a := by rintro ⟨p,hp,_⟩; exact ⟨p.1,hp⟩
theorem star_113_68 (a b : Class α) : Nonempty (Prod a b) ↔ Nonempty a ∧ Nonempty b := by
  constructor
  · rintro ⟨p,ha,hb⟩; exact ⟨⟨p.1,ha⟩,⟨p.2,hb⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩; exact ⟨(x,y),hx,hy⟩

end PM.Architecture.Star113FinalKernel
