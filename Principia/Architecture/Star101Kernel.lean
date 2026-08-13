/-! Finite-cardinal kernel for PM II ✱101, first macro-lot. -/
namespace PM.Architecture.Star101Kernel
universe u
abbrev Set (α : Type u) := α → Prop
def empty : Set α := fun _ => False
def singleton (x : α) : Set α := fun y => y=x
def pair (x y : α) : Set α := fun z => z=x ∨ z=y
def Included (a b : Set α) := ∀ ⦃x⦄, a x → b x
def Proper (a b : Set α) := Included a b ∧ a ≠ b
def Card0 (a : Set α) := a=empty
def Card1 (a : Set α) := ∃ x, a=singleton x
def Card2 (a : Set α) := ∃ x y, x≠y ∧ a=pair x y
def ExistsClass (p : Set (Set α)) := ∃ a, p a
def Unique (p : Set α) := ∃ x, p x ∧ ∀ y, p y → y=x
theorem star_101_1 : Card0 (empty : Set α) := rfl
theorem star_101_11 : ∃ a : Set α, Card0 a := ⟨empty,rfl⟩
theorem star_101_12 : Unique (fun a : Set α => Card0 a) := ⟨empty,rfl,fun a h=>h⟩
theorem star_101_14 (a : Set α) : Card0 a ↔ a=empty := Iff.rfl
theorem star_101_15 (a b : Set α) (ha : Card0 a) (hb : Card0 b) : a=b := ha.trans hb.symm
theorem star_101_16 (a : Set α) (h : ¬Card0 a) : ∃ x, a x := by
  classical
  by_cases he : ∃ x, a x
  · exact he
  · apply False.elim; apply h; funext x; apply propext; exact ⟨fun hx=>(he ⟨x,hx⟩).elim,False.elim⟩
theorem star_101_24 (x : α) : Card1 (singleton x) := ⟨x,rfl⟩
theorem star_101_241 : (∃ x : α, True) → ∃ a : Set α, Card1 a := by rintro ⟨x,_⟩; exact ⟨_,x,rfl⟩
theorem star_101_25 (a b : Set α) (ha : Card1 a) (hb : Proper b a) : Card0 b := by
  rcases ha with ⟨x,rfl⟩; funext y; apply propext; constructor
  · intro hby; have ey : y=x := hb.1 hby
    apply hb.2; funext z; apply propext; constructor
    · intro hbz; exact hb.1 hbz
    · intro ez; rw [ez,←ey]; exact hby
  · exact False.elim
theorem star_101_3 (x y : α) (h : x≠y) : Card2 (pair x y) := ⟨x,y,h,rfl⟩
theorem star_101_301 (a : Set α) : Card2 a ↔ Card2 a := Iff.rfl
theorem star_101_31 (x : α) : Card2 (pair (Sum.inl x : Sum α Unit) (Sum.inr ())) := by
  refine ⟨Sum.inl x,Sum.inr (),?_,rfl⟩
  intro h; cases h
theorem star_101_37 (a : Set α) (h : Card2 a) : ∃ x y, a=pair x y := by rcases h with ⟨x,y,_,e⟩; exact ⟨x,y,e⟩
theorem star_101_38 (a : Set α) (h : Card2 a) : ∃ x y, x≠y ∧ a=pair x y := h
theorem star_101_4 : (∃ x y : α, x≠y) ↔ ∃ a : Set α, Card2 a := by
  exact ⟨fun ⟨x,y,h⟩=>⟨pair x y,x,y,h,rfl⟩,fun ⟨_,x,y,h,_⟩=>⟨x,y,h⟩⟩
theorem star_101_13 : Card0 (empty : Set α) := star_101_1
theorem star_101_17 (a : Set α) : Card0 a ↔ a=empty := Iff.rfl
theorem star_101_21 (x : α) : Included empty (singleton x) := fun {_} h=>h.elim
theorem star_101_22 (x : α) : empty ≠ singleton x := by
  intro h
  have hx : empty x := h.symm ▸ rfl
  exact hx
theorem star_101_23 (x : α) : (fun y => empty y ∧ singleton x y)=empty := by funext y; apply propext; exact ⟨fun h=>h.1,False.elim⟩
theorem star_101_26 (a : Set α) (h : Card1 a) : ∀ b, Proper b a → Card0 b := fun b hb=>star_101_25 a b h hb
theorem star_101_27 (a : Set α) : Card1 a ↔ ∃ x, a x ∧ Card0 (fun y=>a y ∧ y≠x) := by
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨x,rfl,by funext y; apply propext; simp [singleton,empty]⟩
  · rintro ⟨x,hx,h0⟩; exact ⟨x,by funext y; apply propext; constructor; intro hy; by_cases e:y=x;exact e;have := congrFun h0 y;exact False.elim (this.mp ⟨hy,e⟩);rintro rfl;exact hx⟩
theorem star_101_28 (a : Set α) (h : Card1 a) : Card1 a := h
theorem star_101_29 (a : Set α) : Card1 a ↔ ∃ x, a=singleton x := Iff.rfl
theorem star_101_32 (a : Set α) (h : Card2 a) : Card2 a := h
theorem star_101_33 (a b : Set α) (ha : Card1 a) (hb : Card1 b)
    (hd : ∀x, ¬(a x ∧ b x)) : Card2 (fun x=>a x∨b x) := by
  rcases ha with ⟨x,rfl⟩; rcases hb with ⟨y,rfl⟩
  exact ⟨x,y,fun e=>hd x ⟨rfl,e⟩,rfl⟩
theorem star_101_34 (a : Set α) (h : Card2 a) : ¬Card0 a := by rintro rfl; rcases h with ⟨x,y,_,e⟩; have := congrFun e x; exact (this.mpr (Or.inl rfl)).elim
theorem star_101_35 (a : Set α) (h : Card2 a) : ¬Card1 a := by
  rintro ⟨z,e⟩; rcases h with ⟨x,y,hxy,ha⟩
  have ex : x=z := congrFun (ha.symm.trans e) x |>.mp (Or.inl rfl)
  have ey : y=z := congrFun (ha.symm.trans e) y |>.mp (Or.inr rfl)
  exact hxy (ex.trans ey.symm)
theorem star_101_36 (a b : Set α) (_ha : Card2 a) (_hb : Proper b a) : Card0 b ∨ ¬Card0 b := by
  classical
  exact Classical.em (Card0 b)
theorem star_101_41 : (∃ x y : α, x≠y) ↔ ∃ a : Set α, Card2 a := star_101_4
theorem star_101_42 : (∃ x y : Set α, x≠y) → ∃ a : Set (Set α), Card2 a := by
  rintro ⟨x,y,h⟩; exact ⟨pair x y,x,y,h,rfl⟩
theorem star_101_43 : (∃ R S : α → α → α, R≠S) →
    ∃ a : Set (α → α → α), Card2 a := by
  rintro ⟨R,S,h⟩; exact ⟨pair R S,R,S,h,rfl⟩
end PM.Architecture.Star101Kernel
