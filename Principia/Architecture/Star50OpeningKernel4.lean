namespace PM.Architecture.Star50OpeningKernel4

universe u

abbrev Relation (α : Sort u) := α → α → Prop
abbrev ClassExtension (α : Sort u) := α → Prop

def I : Relation α := fun x y => x = y
def J : Relation α := fun x y => x ≠ y
def converse (R : Relation α) : Relation α := fun x y => R y x
def comp (R S : Relation α) : Relation α := fun x z => ∃ y, R x y ∧ S y z
def interR (R S : Relation α) : Relation α := fun x y => R x y ∧ S x y
def emptyR : Relation α := fun _ _ => False
def interC (A B : ClassExtension α) : ClassExtension α := fun x => A x ∧ B x
def emptyC : ClassExtension α := fun _ => False
def leftRestrict (A : ClassExtension α) (R : Relation α) : Relation α :=
  fun x y => A x ∧ R x y
def rightRestrict (R : Relation α) (A : ClassExtension α) : Relation α :=
  fun x y => R x y ∧ A y
def bothRestrict (A : ClassExtension α) (R : Relation α) (B : ClassExtension α) :
    Relation α := fun x y => A x ∧ R x y ∧ B y
def domain (R : Relation α) : ClassExtension α := fun x => ∃ y, R x y
def converseDomain (R : Relation α) : ClassExtension α := fun y => ∃ x, R x y
def field (R : Relation α) : ClassExtension α :=
  fun x => domain R x ∨ converseDomain R x
def cross (A B : ClassExtension α) : Relation α := fun x y => A x ∧ B y
def image (R : Relation α) (B : ClassExtension α) : ClassExtension α :=
  fun x => ∃ y, B y ∧ R x y
def Included (R S : Relation α) : Prop := ∀ x y, R x y → S x y

private theorem relationExt {R S : Relation α} (h : ∀ x y, R x y ↔ S x y) :
    R = S := by funext x y; exact propext (h x y)
private theorem classExt {A B : ClassExtension α} (h : ∀ x, A x ↔ B x) :
    A = B := by funext x; exact propext (h x)

/-- PM I ✱50·51. -/
theorem star_50_51 (A : ClassExtension α) :
    converse (leftRestrict A I) = leftRestrict A I := by
  apply relationExt
  intro x y
  constructor
  · rintro ⟨hy, hyx⟩
    subst y
    exact ⟨hy, rfl⟩
  · rintro ⟨hx, hxy⟩
    subst y
    exact ⟨hx, rfl⟩

/-- PM I ✱50·52, retaining domain, converse domain, and field. -/
theorem star_50_52 (A : ClassExtension α) :
    domain (leftRestrict A I) = A ∧
    converseDomain (leftRestrict A I) = A ∧
    field (leftRestrict A I) = A := by
  have hd : domain (leftRestrict A I) = A := by
    apply classExt; intro x; constructor
    · rintro ⟨y, hx, _⟩; exact hx
    · intro hx; exact ⟨x, hx, rfl⟩
  have hc : converseDomain (leftRestrict A I) = A := by
    apply classExt; intro y; constructor
    · rintro ⟨x, hx, hxy⟩; cases hxy; exact hx
    · intro hy; exact ⟨y, hy, rfl⟩
  refine ⟨hd, hc, ?_⟩
  apply classExt; intro x; constructor
  · rintro (hx | hx)
    · simpa [hd] using hx
    · simpa [hc] using hx
  · intro hx; exact Or.inl (by simpa [hd] using hx)

/-- PM I ✱50·53. -/
theorem star_50_53 (A B : ClassExtension α) :
    bothRestrict A I B = leftRestrict (interC A B) I ∧
    leftRestrict (interC A B) I = rightRestrict I (interC A B) := by
  constructor <;> apply relationExt <;> intro x y <;> constructor
  · rintro ⟨hx, rfl, hy⟩; exact ⟨⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨hx, hy⟩, rfl⟩; exact ⟨hx, rfl, hy⟩
  · rintro ⟨⟨hx, hy⟩, rfl⟩; exact ⟨rfl, hx, hy⟩
  · rintro ⟨rfl, hx, hy⟩; exact ⟨⟨hx, hy⟩, rfl⟩

/-- PM I ✱50·54. -/
theorem star_50_54 (A : ClassExtension α) :
    comp (leftRestrict A I) (leftRestrict A I) = leftRestrict A I := by
  apply relationExt; intro x z; constructor
  · rintro ⟨y, ⟨hx, hxy⟩, _, hyz⟩; subst y; subst z; exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨x, ⟨hx, rfl⟩, hx, rfl⟩

/-- PM I ✱50·55. -/
theorem star_50_55 (A B : ClassExtension α) :
    interC A B = emptyC ↔ Included (cross A B) J := by
  constructor
  · intro h x y hxy heq
    subst y
    have point := congrFun h x
    exact Eq.mp point hxy
  · intro h
    apply classExt; intro x; constructor
    · intro hx; exact False.elim (h x x hx rfl)
    · exact False.elim

/-- PM I ✱50·56. -/
theorem star_50_56 (A B : ClassExtension α) :
    (∃ x, interC A B x) ↔ ∃ x y, interR (cross A B) I x y := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, x, hx, rfl⟩
  · rintro ⟨x, y, hxy, heq⟩; subst y; exact ⟨x, hxy⟩

/-- PM I ✱50·57. -/
theorem star_50_57 (A : ClassExtension α) (R : Relation α) :
    interR I (leftRestrict A R) = interR I (rightRestrict R A) ∧
    interR I (rightRestrict R A) = interR I (bothRestrict A R A) := by
  constructor <;> apply relationExt <;> intro x y <;> constructor
  · rintro ⟨rfl, hx, hR⟩; exact ⟨rfl, hR, hx⟩
  · rintro ⟨rfl, hR, hy⟩; exact ⟨rfl, hy, hR⟩
  · rintro ⟨rfl, hR, hy⟩; exact ⟨rfl, hy, hR, hy⟩
  · rintro ⟨rfl, hx, hR, _⟩; exact ⟨rfl, hR, hx⟩

private theorem includedJ_iff_diagonal (R : Relation α) :
    Included R J ↔ ∀ x, ¬ R x x := by
  constructor
  · intro h x hx; exact h x x hx rfl
  · intro h x y hxy heq; subst y; exact h x hxy

/-- PM I ✱50·58, retaining all three equivalent restrictions. -/
theorem star_50_58 (A : ClassExtension α) (R : Relation α) :
    (Included (leftRestrict A R) J ↔ Included (rightRestrict R A) J) ∧
    (Included (rightRestrict R A) J ↔ Included (bothRestrict A R A) J) := by
  simp only [includedJ_iff_diagonal]
  constructor <;> constructor <;> intro h x hx
  · exact h x ⟨hx.2, hx.1⟩
  · exact h x ⟨hx.2, hx.1⟩
  · exact h x ⟨hx.2.1, hx.1⟩
  · exact h x ⟨hx.2, hx.1, hx.2⟩

/-- PM I ✱50·59. -/
theorem star_50_59 (A B : ClassExtension α) :
    image (rightRestrict I A) B = interC A B := by
  apply classExt; intro x; constructor
  · rintro ⟨y, hy, hxy, hAy⟩; subst y; exact ⟨hAy, hy⟩
  · rintro ⟨hxA, hxB⟩; exact ⟨x, hxB, rfl, hxA⟩

end PM.Architecture.Star50OpeningKernel4
