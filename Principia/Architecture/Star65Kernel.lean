namespace PM.Architecture.Star65Kernel

universe u
abbrev Class (α : Type u) := α → Prop
abbrev Relation (α : Type u) := α → α → Prop

def inter (A B : Class α) : Class α := fun x => A x ∧ B x
def Included (A B : Class α) := ∀ x, A x → B x
def left (A : Class α) (R : Relation α) : Relation α := fun x y => A x ∧ R x y
def right (R : Relation α) (B : Class α) : Relation α := fun x y => R x y ∧ B y
def both (A : Class α) (R : Relation α) (B : Class α) := left A (right R B)
def image (R : Relation α) (A : Class α) : Class α := fun x => ∃ y, A y ∧ R x y
def classSub (A T : Class α) := inter A T
def classParen (A T2 : Class α) := inter A T2
def relSub (R : Relation α) (T : Class α) := left T R
def relParen (R : Relation α) (T2 : Class α) := left T2 R
def relPair (R : Relation α) (TX TY : Class α) := both TX R TY
def relMixed (R : Relation α) (T2X TY : Class α) := both T2X R TY
def relParenPair (R : Relation α) (T2X T2Y : Class α) := both T2X R T2Y

private theorem classExt {A B : Class α} (h : ∀ x, A x ↔ B x) : A = B := by
  funext x; exact propext (h x)
private theorem relExt {R S : Relation α} (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y; exact propext (h x y)
private theorem both_idem (R : Relation α) (TX TY : Class α) :
    both TX (both TX R TY) TY = both TX R TY := by
  apply relExt; intro x y; simp [both, left, right, and_assoc]

/-- ✱65·01. `αₓ = α ∩ tʻx` Df. -/
def star_65_01 (A T : Class α) : Class α := inter A T
/-- ✱65·02. `α(x) = α ∩ tʻtʻx` Df. -/
def star_65_02 (A T2 : Class α) : Class α := inter A T2
/-- ✱65·03. `Rₓ = (tʻx) ◁ R` Df. -/
def star_65_03 (R : Relation α) (T : Class α) : Relation α := left T R
/-- ✱65·04. `R(x) = (t²ʻx) ◁ R` Df. -/
def star_65_04 (R : Relation α) (T2 : Class α) : Relation α := left T2 R
/-- ✱65·1. `R_(x,y) = (tʻx) ◁ R ▷ (tʻy)` Df. -/
def star_65_1 (R : Relation α) (TX TY : Class α) : Relation α := both TX R TY
/-- ✱65·11. `R(x_y) = (t²ʻx) ◁ R ▷ (tʻy)` Df. -/
def star_65_11 (R : Relation α) (T2X TY : Class α) : Relation α := both T2X R TY
/-- ✱65·12. `R(x,y) = (t²ʻx) ◁ R ▷ (t²ʻy)` Df. -/
def star_65_12 (R : Relation α) (T2X T2Y : Class α) : Relation α := both T2X R T2Y

/-- ✱65·13. -/
theorem star_65_13 (A B T : Class α) (hBT : Included B T) :
    (A = classSub B T ↔ A = inter T B) ∧
    (A = inter T B ↔ Included A T ∧ A = B) := by
  constructor
  · constructor <;> intro h <;> subst A <;> apply classExt <;> intro x
    · exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    · exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · constructor
    · intro hAB
      constructor
      · intro x hx; rw [hAB] at hx; exact hx.1
      · apply classExt; intro x; constructor
        · intro hx; rw [hAB] at hx; exact hx.2
        · intro hx; rw [hAB]; exact ⟨hBT x hx, hx⟩
    · rintro ⟨h, rfl⟩; apply classExt; intro x; exact ⟨fun hx => ⟨h x hx, hx⟩, And.right⟩

/-- ✱65·14. -/
theorem star_65_14 (G T2X TA : Class α) (h : T2X = TA) : classParen G T2X = classSub G TA := by simp [classParen, classSub, h]
/-- ✱65·15. -/
theorem star_65_15 (R : Relation α) (T2X TA TY TG : Class α) (h : T2X = TA) (hy : TY = TG) :
    relParen R T2X = relSub R TA ∧ relMixed R T2X TY = relPair R TA TG := by
  subst T2X; subst TY; exact ⟨rfl, rfl⟩
/-- ✱65·16. -/
theorem star_65_16 (R : Relation α) (T2X TA T2Y TB : Class α) (hx : T2X = TA) (hy : T2Y = TB) :
    relParenPair R T2X T2Y = relMixed R T2X TB ∧ relMixed R T2X TB = relPair R TA TB := by subst T2X; subst T2Y; exact ⟨rfl, rfl⟩

def forwardSection (R : Relation α) (TX TY : Class α) (y : α) : Class α := fun x => relPair R TX TY x y
def singletonGeneration (R : Relation α) (TX TY : Class α) (y : α) : Class α := forwardSection R TX TY y
/-- ✱65·2. -/
theorem star_65_2 (R : Relation α) (TX TY : Class α) (y : α) : singletonGeneration R TX TY y = forwardSection R TX TY y := rfl

/-- ✱65·21. -/
theorem star_65_21 (R : Relation α) (TX TY : Class α) : relPair (relPair R TX TY) TX TY = relPair R TX TY := by
  exact both_idem R TX TY
/-- ✱65·22. -/
theorem star_65_22 (R : Relation α) (TX TY : Class α) : relParenPair (relParenPair R TX TY) TX TY = relParenPair R TX TY := by
  exact both_idem R TX TY
/-- ✱65·23. -/
theorem star_65_23 (R : Relation α) (TX TY : Class α) : relMixed (relMixed R TX TY) TX TY = relMixed R TX TY := by
  exact both_idem R TX TY
/-- ✱65·24. -/
theorem star_65_24 (R : Relation α) (T : Class α) : relSub (relSub R T) T = relSub R T := by
  apply relExt; intro x y; simp [relSub, left]
/-- ✱65·25. -/
theorem star_65_25 (R : Relation α) (T : Class α) : relParen (relParen R T) T = relParen R T := star_65_24 R T

/-- ✱65·3. -/
theorem star_65_3 (R : Relation α) (T M : Class α) :
    image (relSub R T) M = classSub (image R M) T ∧ classSub (image R M) T = inter (image R M) T := by
  constructor
  · apply classExt; intro x; constructor
    · rintro ⟨y, hy, hT, hR⟩; exact ⟨⟨y, hy, hR⟩, hT⟩
    · rintro ⟨⟨y, hy, hR⟩, hT⟩; exact ⟨y, hy, hT, hR⟩
  · rfl

end PM.Architecture.Star65Kernel
