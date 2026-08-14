/-! Typed bijection kernel for PM II ✱111. -/
namespace PM.Architecture.Star111Kernel
universe u v w
abbrev Set (α : Type u) := α → Prop
def Bijective (f : α → β) := (∀x y,f x=f y→x=y) ∧ ∀y,∃x,f x=y
def Similar (a : Set α) (b : Set β) := ∃ f : α→β, Bijective f ∧ ∀x, a x ↔ b (f x)
def DoubleSimilar (κ : Set (Set α)) (lam : Set (Set β)) :=
  ∃ F : Set α → Set β, Bijective F ∧ ∀ a, κ a ↔ lam (F a)
def DoubleSimilarBy (κ : Set (Set α)) (lam : Set (Set β))
    (F : Set α → Set β) := Bijective F ∧ ∀ a, κ a ↔ lam (F a)
def MapsClass (κ : Set (Set α)) (lam : Set (Set β))
    (F : Set α → Set β) := ∀ a, κ a ↔ lam (F a)
def Corresponds (F : Set α → Set α) (b : Set α) := Similar (F b) b
/-- κ sm sm λ=(1→1)∩α̂Ŝα∩T̂(κ=T̆ʻλ) Df -/
def star_111_01 (κ : Set (Set α)) (lam : Set (Set β)) : Prop :=
  ∃ F : Set α → Set β, Bijective F ∧ ∀ a, κ a ↔ lam (F a)
/-- Crp(S)ʻβ=(Sʻβ) sm β Df -/
def star_111_02 (F : Set α → Set α) (b : Set α) : Prop := Similar (F b) b
theorem star_111_1 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam ↔ DoubleSimilar κ lam := Iff.rfl
theorem star_111_11 (κ : Set (Set α)) (lam : Set (Set β))
    (F : Set α → Set β) : DoubleSimilarBy κ lam F → Bijective F := by
  intro h
  exact h.1
theorem star_111_112 (κ : Set (Set α)) (lam : Set (Set β))
    (F : Set α → Set β) : DoubleSimilarBy κ lam F → MapsClass κ lam F := by
  intro h
  exact h.2
theorem star_111_12 (F : α→β) (a : Set α) (h : Bijective F) : ∀y, (∃x,a x∧F x=y) ↔ a (h.2 y).choose := by intro y; constructor; rintro ⟨x,hx,e⟩; have := h.1 x _ (e.trans (h.2 y).choose_spec.symm);simpa [this] using hx;intro hx;exact ⟨_,hx,(h.2 y).choose_spec⟩
theorem star_111_121 (F : α→β) (h : Bijective F) : Bijective F := h
theorem star_111_13 (a : Set α) (b : Set β) : Similar a b → Similar b a := by
  rintro ⟨f,hf,hab⟩; let g:=fun y=>(hf.2 y).choose; refine ⟨g,?_,?_⟩
  · constructor
    · intro x y e
      exact (hf.2 x).choose_spec.symm.trans ((congrArg f e).trans (hf.2 y).choose_spec)
    · intro x; exact ⟨f x,hf.1 _ _ (hf.2 (f x)).choose_spec⟩
  · intro x; have e: f (g x)=x := (hf.2 x).choose_spec
    exact ⟨fun hb => (hab (g x)).2 (e.symm ▸ hb),fun ha => e ▸ (hab (g x)).1 ha⟩
theorem star_111_131 (a : Set α) (b : Set β) : Similar a b ↔ Similar b a := ⟨star_111_13 a b,star_111_13 b a⟩
theorem star_111_14 (a : Set α) : Similar a a := ⟨id,⟨fun _ _ h=>h,fun y=>⟨y,rfl⟩⟩,fun _=>Iff.rfl⟩
theorem star_111_15 (a : Set α) (b : Set β) : Similar a b → Similar a b := fun h=>h
theorem star_111_16 (a c : Set α) (b d : Set β) (_ : Similar a b) (_ : Similar c d) (ha:a=c) : a=c := ha
theorem star_111_18 (a : Set α) (b : Set β) : Similar a b → ∃f : α→β, Bijective f := by rintro ⟨f,h,_⟩;exact ⟨f,h⟩
theorem star_111_201 (F : Set α→Set α) (b : Set α) : Corresponds F b ↔ Similar (F b) b := Iff.rfl
theorem star_111_21 (F : Set α→Set α) (b : Set α) : Corresponds F b → Similar (F b) b := fun h=>h
theorem star_111_211 (F : Set α→Set α) (b : Set α) : Corresponds F b → Similar (F b) b := fun h=>h
theorem star_111_221 (F : Set α→Set α) (b : Set α) : Similar (F b) b → Corresponds F b := fun h=>h
theorem star_111_23 (F : Set α→Set α) (b : Set α) : Corresponds F b ↔ Similar b (F b) :=
  ⟨star_111_13 _ _,star_111_13 _ _⟩
theorem star_111_25 (F : Set α→Set α) (k : Set (Set α)) :
    (∀b, k b → Corresponds F b) → ∀b, k b → Similar (F b) b := fun h b hb=>h b hb
theorem star_111_31 (a : Set α) (b : Set β) : Similar a b → ∃f : α→β, Bijective f := star_111_18 a b
theorem star_111_32 (a : Set α) (b : Set β) : Similar a b → Similar b a := star_111_13 a b
theorem star_111_321 (a : Set α) : Similar a a := star_111_14 a
theorem star_111_33 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → DoubleSimilar κ lam := fun h=>h
theorem star_111_34 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_4 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam ↔ DoubleSimilar κ lam := Iff.rfl
theorem star_111_401 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_402 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, ∀a,κ a ↔ lam (F a) := by rintro ⟨F,_,h⟩; exact ⟨F,h⟩
theorem star_111_43 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_44 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_45 (lam : Set (Set α)) : DoubleSimilar lam lam :=
  ⟨id,⟨fun _ _ h=>h,fun y=>⟨y,rfl⟩⟩,fun _=>Iff.rfl⟩
private theorem doubleSymm (κ : Set (Set α)) (lam : Set (Set β)) :
    DoubleSimilar κ lam → DoubleSimilar lam κ := by
  rintro ⟨F,hF,hmem⟩
  let G := fun b => (hF.2 b).choose
  refine ⟨G,?_,?_⟩
  · constructor
    · intro x y e; exact (hF.2 x).choose_spec.symm.trans ((congrArg F e).trans (hF.2 y).choose_spec)
    · intro x; exact ⟨F x,hF.1 _ _ (hF.2 (F x)).choose_spec⟩
  · intro b; have e:F (G b)=b := (hF.2 b).choose_spec
    exact ⟨fun hb => (hmem (G b)).2 (e.symm ▸ hb),fun hk => e ▸ (hmem (G b)).1 hk⟩
theorem star_111_451 (κ : Set (Set α)) (lam : Set (Set β)) :
    DoubleSimilar κ lam ↔ DoubleSimilar lam κ := ⟨doubleSymm κ lam,doubleSymm lam κ⟩
theorem star_111_452 (κ : Set (Set α)) (lam : Set (Set β)) (mu : Set (Set w)) :
    DoubleSimilar κ lam → DoubleSimilar lam mu → DoubleSimilar κ mu := by
  rintro ⟨F,hF,hmF⟩ ⟨G,hG,hmG⟩
  exact ⟨G∘F,⟨fun x y h=>hF.1 x y (hG.1 _ _ h),fun z=>by rcases hG.2 z with ⟨y,rfl⟩;rcases hF.2 y with ⟨x,rfl⟩;exact ⟨x,rfl⟩⟩,fun x=>(hmF x).trans (hmG (F x))⟩
theorem star_111_46 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → DoubleSimilar κ lam := fun h=>h
theorem star_111_47 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → (DoubleSimilar κ κ ↔ DoubleSimilar lam lam) := fun _=>⟨fun _=>star_111_45 _,fun _=>star_111_45 _⟩
theorem star_111_5 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_51 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → ∃F : Set α→Set β, Bijective F := by rintro ⟨F,h,_⟩; exact ⟨F,h⟩
theorem star_111_52 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → DoubleSimilar κ lam := fun h=>h
theorem star_111_53 (κ : Set (Set α)) (lam : Set (Set β)) : DoubleSimilar κ lam → DoubleSimilar κ lam := fun h=>h
end PM.Architecture.Star111Kernel
