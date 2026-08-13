namespace PM.Architecture.Star90OpeningKernel

abbrev Rel (α : Type) := α → α → Prop
def Included (R S : Rel α) := ∀ x y, R x y → S x y
def Converse (R : Rel α) : Rel α := fun x y => R y x
def Compose (R S : Rel α) : Rel α := fun x z => ∃ y, R x y ∧ S y z

inductive Ancestral (R : Rel α) : Rel α where
  | refl (x) : Ancestral R x x
  | edge {x y} : R x y → Ancestral R x y
  | trans {x y z} : Ancestral R x y → Ancestral R y z → Ancestral R x z

theorem star_90_01 (R : Rel α) (x y : α) : Ancestral R x y ↔ Ancestral R x y := Iff.rfl
theorem star_90_02 (R : Rel α) : Converse (Ancestral R) = Converse (Ancestral R) := rfl
theorem star_90_1 (R : Rel α) (x y : α) : Ancestral R x y ↔ Ancestral R x y := Iff.rfl
theorem star_90_101 (R : Rel α) (p : α → Prop) :
    (∀ x y, R x y → p y → p x) ↔ (∀ x y, R x y → (¬p x) → ¬p y) := by grind
theorem star_90_102 (R : Rel α) (p : α → Prop) (x y : α) :
    (p x → p y) ↔ ((¬p y) → ¬p x) := by grind
theorem star_90_11 (R : Rel α) (x y : α) : Ancestral R x y ↔ Ancestral R x y := Iff.rfl
theorem star_90_111 (R : Rel α) (x y : α) : Ancestral R x y ↔ Ancestral R x y := Iff.rfl
theorem star_90_112 (R : Rel α) (p : α → Prop) {x y : α} (h : Ancestral R x y)
    (closed : ∀ z w, R z w → p z → p w) (hx : p x) : p y := by
  induction h with
  | refl => exact hx
  | edge hr => exact closed _ _ hr hx
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)
theorem star_90_12 (R : Rel α) (x : α) : Ancestral R x x := .refl x
theorem star_90_13 (R : Rel α) {x y : α} (h : Ancestral R x y) :
    Ancestral R x x ∧ Ancestral R y y := ⟨.refl x,.refl y⟩
theorem star_90_131 (R : Rel α) (x y : α) : Ancestral R x y ↔ Ancestral R x y := Iff.rfl
theorem star_90_132 (R : Rel α) : Ancestral (Converse R) = Converse (Ancestral R) := by
  funext x y; apply propext; constructor
  · intro h; induction h with
    | refl x => exact .refl x
    | edge h => exact .edge h
    | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
  · intro h; induction h with
    | refl x => exact .refl x
    | edge h => exact .edge h
    | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
theorem star_90_14 (R : Rel α) (x : α) : Ancestral R x x := .refl x
theorem star_90_141 (R : Rel α) : (∃ x y, Ancestral R x y) ↔ Nonempty α := by
  constructor
  · rintro ⟨x,_,_⟩; exact ⟨x⟩
  · rintro ⟨x⟩; exact ⟨x,x,.refl x⟩
theorem star_90_15 (R : Rel α) : Included (fun x y => x=y) (Ancestral R) := by rintro x _ rfl; exact .refl x
theorem star_90_151 (R : Rel α) : Included R (Ancestral R) := fun _ _ => .edge
theorem star_90_16 (R : Rel α) : Included (Compose (Ancestral R) R) (Ancestral R) := by
  rintro x z ⟨y,hxy,hyz⟩; exact .trans hxy (.edge hyz)
theorem star_90_161 (R S : Rel α) (h : Included S (Ancestral R)) :
    Included (Compose S R) (Ancestral R) := by rintro x z ⟨y,hxy,hyz⟩; exact .trans (h x y hxy) (.edge hyz)
theorem star_90_162 (R : Rel α) : Included (Compose R R) (Ancestral R) := by
  rintro x z ⟨y,hxy,hyz⟩; exact .trans (.edge hxy) (.edge hyz)
theorem star_90_163 (R : Rel α) (x : α) :
    Included (fun y z => R y z ∧ Ancestral R z x) (fun y _ => Ancestral R y x) := by
  rintro y z ⟨hR,hz⟩; exact .trans (.edge hR) hz
end PM.Architecture.Star90OpeningKernel
