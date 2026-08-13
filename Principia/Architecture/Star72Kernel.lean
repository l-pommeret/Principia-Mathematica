namespace PM.Architecture.Star72Kernel

abbrev Rel (α β : Type) := α → β → Prop
abbrev Class (α : Type) := α → Prop

def Converse (R : Rel α β) : Rel β α := fun y x => R x y
def Compose (R : Rel β γ) (S : Rel α β) : Rel α γ := fun x z => ∃ y, S x y ∧ R y z
def Domain (R : Rel α β) : Class α := fun x => ∃ y, R x y
def Range (R : Rel α β) : Class β := fun y => ∃ x, R x y
def Image (R : Rel α β) (A : Class α) : Class β := fun y => ∃ x, A x ∧ R x y
def Preimage (R : Rel α β) (B : Class β) : Class α := fun x => ∃ y, B y ∧ R x y
def Functional (R : Rel α β) : Prop := ∀ ⦃x y z⦄, R x y → R x z → y = z
def Injective (R : Rel α β) : Prop := ∀ ⦃x z y⦄, R x y → R z y → x = z
def OneOne (R : Rel α β) : Prop := Functional R ∧ Injective R
def Subrelation (S R : Rel α β) : Prop := ∀ ⦃x y⦄, S x y → R x y
def RestrictDomain (R : Rel α β) (A : Class α) : Rel α β := fun x y => A x ∧ R x y
def RestrictRange (R : Rel α β) (B : Class β) : Rel α β := fun x y => R x y ∧ B y
def Difference (R S : Rel α β) : Rel α β := fun x y => R x y ∧ ¬ S x y
def Inter (A B : Class α) : Class α := fun x => A x ∧ B x
def Included (A B : Class α) : Prop := ∀ ⦃x⦄, A x → B x

variable {α : Type} {R S : Rel α α}

theorem converse_converse (R : Rel α β) : Converse (Converse R) = R := rfl
theorem converse_functional_iff_injective (R : Rel α β) : Functional (Converse R) ↔ Injective R := by
  exact ⟨fun h _ _ _ a b => h a b, fun h _ _ _ a b => h a b⟩
theorem converse_injective_iff_functional (R : Rel α β) : Injective (Converse R) ↔ Functional R := by
  exact ⟨fun h _ _ _ a b => h a b, fun h _ _ _ a b => h a b⟩
theorem converse_oneOne (R : Rel α β) : OneOne (Converse R) ↔ OneOne R := by
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨(converse_injective_iff_functional R).mp hi,
      (converse_functional_iff_injective R).mp hf⟩
  · rintro ⟨hf, hi⟩
    exact ⟨(converse_functional_iff_injective R).mpr hi,
      (converse_injective_iff_functional R).mpr hf⟩

theorem star_72_2 (hR : Functional R) (hS : Functional S) : Functional (Compose R S) := by
  rintro x z₁ z₂ ⟨y₁, hs₁, hr₁⟩ ⟨y₂, hs₂, hr₂⟩
  have e : y₁ = y₂ := hS hs₁ hs₂
  subst e
  exact hR hr₁ hr₂

theorem star_72_201 (hR : Injective R) (hS : Injective S) :
    Injective (Compose R S) := by
  rintro z x₁ x₂ ⟨y₁, hs₁, hr₁⟩ ⟨y₂, hs₂, hr₂⟩
  have : y₁ = y₂ := hR hr₁ hr₂
  subst this
  exact hS hs₁ hs₂

theorem star_72_202 (hR : OneOne R) (hS : OneOne S) : OneOne (Compose R S) :=
  ⟨star_72_2 hR.1 hS.1, star_72_201 hR.2 hS.2⟩

theorem star_72_21 (hR : Functional R) (hS : Functional S) :
    Domain (Compose R S) x ↔ ∃ y, S x y ∧ Domain R y := by
  constructor
  · rintro ⟨z, y, hs, hr⟩; exact ⟨y, hs, ⟨z, hr⟩⟩
  · rintro ⟨y, hs, z, hr⟩; exact ⟨z, y, hs, hr⟩

theorem star_72_211 (hR : Injective R) (hS : Injective S) :
    Range (Compose R S) z ↔ ∃ y, Range S y ∧ R y z := by
  constructor
  · rintro ⟨x, y, hs, hr⟩; exact ⟨y, ⟨x, hs⟩, hr⟩
  · rintro ⟨y, ⟨x, hs⟩, hr⟩; exact ⟨x, y, hs, hr⟩

theorem star_72_24 (h : OneOne R) :
    Domain R x ↔ Compose (Converse R) R x x := by
  constructor
  · rintro ⟨y, hr⟩; exact ⟨y, hr, hr⟩
  · rintro ⟨y, hxy, _⟩; exact ⟨y, hxy⟩

theorem star_72_241 (h : OneOne R) :
    Range R y ↔ Compose R (Converse R) y y := by
  constructor
  · rintro ⟨x, hr⟩; exact ⟨x, hr, hr⟩
  · rintro ⟨x, hyx, _⟩; exact ⟨x, hyx⟩

theorem star_72_4 (h : Injective R) (A B : Class α) :
    Inter (Image R A) (Image R B) = Image R (Inter A B) := by
  funext y; apply propext; constructor
  · rintro ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
    have : x = z := h hxy hzy
    subst this; exact ⟨x, ⟨hxA, hzB⟩, hxy⟩
  · rintro ⟨x, ⟨hxA, hxB⟩, hxy⟩
    exact ⟨⟨x, hxA, hxy⟩, ⟨x, hxB, hxy⟩⟩

theorem star_72_401 (h : Functional R) (A B : Class α) :
    Inter (Preimage R A) (Preimage R B) = Preimage R (Inter A B) := by
  funext x; apply propext; constructor
  · rintro ⟨⟨y, hyA, hxy⟩, ⟨z, hzB, hxz⟩⟩
    have : y = z := h hxy hxz
    subst this; exact ⟨y, ⟨hyA, hzB⟩, hxy⟩
  · rintro ⟨y, ⟨hyA, hyB⟩, hxy⟩
    exact ⟨⟨y, hyA, hxy⟩, ⟨y, hyB, hxy⟩⟩

theorem star_72_43 (h : Injective R) (e : Image R A = Image R B) :
    Inter A (Domain R) = Inter B (Domain R) := by
  funext x; apply propext; constructor
  · rintro ⟨hxA, y, hxy⟩; refine ⟨?_, ⟨y, hxy⟩⟩
    have : Image R B y := e ▸ ⟨x, hxA, hxy⟩
    rcases this with ⟨z, hzB, hzy⟩
    exact (@h x z y hxy hzy) ▸ hzB
  · rintro ⟨hxB, y, hxy⟩; refine ⟨?_, ⟨y, hxy⟩⟩
    have : Image R A y := e.symm ▸ ⟨x, hxB, hxy⟩
    rcases this with ⟨z, hzA, hzy⟩
    exact (@h x z y hxy hzy) ▸ hzA

theorem star_72_44 (h : Injective R) (hA : Included A (Domain R))
    (hB : Included B (Domain R)) (e : Image R A = Image R B) : A = B := by
  have q := star_72_43 h e
  funext x; apply propext
  exact ⟨fun hx => (congrFun q x |>.mp ⟨hx, hA hx⟩).1,
    fun hx => (congrFun q x |>.mpr ⟨hx, hB hx⟩).1⟩

theorem star_72_46 (h : Injective R) :
    Image R A = Image R B ↔ Inter A (Domain R) = Inter B (Domain R) := by
  constructor
  · exact star_72_43 h
  · intro e; funext y; apply propext; constructor
    · rintro ⟨x, hxA, hxy⟩
      have hx := congrFun e x |>.mp ⟨hxA, ⟨y, hxy⟩⟩
      exact ⟨x, hx.1, hxy⟩
    · rintro ⟨x, hxB, hxy⟩
      have hx := congrFun e x |>.mpr ⟨hxB, ⟨y, hxy⟩⟩
      exact ⟨x, hx.1, hxy⟩

theorem star_72_5 (h : Injective R) :
    Preimage R (Image R A) = Inter A (Domain R) := by
  funext x; apply propext; constructor
  · rintro ⟨y, ⟨z, hzA, hzy⟩, hxy⟩
    exact ⟨(@h x z y hxy hzy) ▸ hzA, ⟨y, hxy⟩⟩
  · rintro ⟨hxA, y, hxy⟩; exact ⟨y, ⟨x, hxA, hxy⟩, hxy⟩

theorem star_72_501 (h : Functional R) :
    Image R (Preimage R B) = Inter B (Range R) := by
  funext y; apply propext; constructor
  · rintro ⟨x, ⟨z, hzB, hxz⟩, hxy⟩
    exact ⟨(@h x y z hxy hxz) ▸ hzB, ⟨x, hxy⟩⟩
  · rintro ⟨hyB, x, hxy⟩; exact ⟨x, ⟨y, hyB, hxy⟩, hxy⟩

theorem star_72_502 (h : Injective R) (hA : Included A (Domain R)) :
    Preimage R (Image R A) = A := by
  rw [star_72_5 h]; funext x; apply propext
  exact ⟨And.left, fun hx => ⟨hx, hA hx⟩⟩

theorem star_72_503 (h : Functional R) (hB : Included B (Range R)) :
    Image R (Preimage R B) = B := by
  rw [star_72_501 h]; funext y; apply propext
  exact ⟨And.left, fun hy => ⟨hy, hB hy⟩⟩

theorem star_72_512 (h : Functional R) (hB : Included B (Range R)) (hxy : R x y) :
    (B y ↔ Preimage R B x) := by
  constructor
  · exact fun hy => ⟨y, hy, hxy⟩
  · rintro ⟨z, hz, hxz⟩; exact h hxz hxy ▸ hz

theorem star_72_59 (h : Injective R) :
    Compose (Converse R) R x z ↔ x = z ∧ Domain R x := by
  constructor
  · rintro ⟨y, hxy, hzy⟩; exact ⟨h hxy hzy, ⟨y, hxy⟩⟩
  · rintro ⟨rfl, y, hxy⟩; exact ⟨y, hxy, hxy⟩

theorem star_72_591 (h : Functional R) :
    Compose R (Converse R) x z ↔ x = z ∧ Range R x := by
  exact star_72_59 (R := Converse R) ((converse_injective_iff_functional R).mpr h)

theorem star_72_62 (h : Injective R) :
    Compose (Converse R) R x z → x = z := by
  intro q; exact (star_72_59 (R := R) (x := x) (z := z) h).mp q |>.1

theorem star_72_621 (h : Functional R) :
    Compose (Converse R) R x z ↔ ∃ y, R x y ∧ R z y := Iff.rfl

theorem star_72_7 (h : Functional R) (A : Class α) :
    Functional (RestrictDomain R A) := fun _ _ _ h₁ h₂ => h h₁.2 h₂.2

theorem star_72_71 (h : Injective R) (B : Class α) :
    Injective (RestrictRange R B) := fun _ _ _ h₁ h₂ => h h₁.1 h₂.1

theorem star_72_72 (h : OneOne R) (A B : Class α) :
    OneOne (RestrictRange (RestrictDomain R A) B) :=
  ⟨fun _ _ _ h₁ h₂ => h.1 h₁.1.2 h₂.1.2,
   fun _ _ _ h₁ h₂ => h.2 h₁.1.2 h₂.1.2⟩

theorem star_72_9 (h : Injective R) (hs : Subrelation S R) :
    S x y ↔ R x y ∧ Range S y := by
  exact ⟨fun q => ⟨hs q, ⟨x, q⟩⟩,
    fun ⟨rxy, z, szy⟩ => by
      have e : z = x := @h z x y (hs szy) rxy
      exact e ▸ szy⟩

theorem star_72_91 (h : Injective R) (hs : Subrelation S R) :
    Range (Difference R S) y ↔ Range R y ∧ ¬ Range S y := by
  constructor
  · rintro ⟨x, rxy, nsxy⟩; refine ⟨⟨x, rxy⟩, ?_⟩
    rintro ⟨z, szy⟩; exact nsxy ((star_72_9 h hs).mpr ⟨rxy, ⟨z, szy⟩⟩)
  · rintro ⟨⟨x, rxy⟩, hn⟩; exact ⟨x, rxy, fun sxy => hn ⟨x, sxy⟩⟩

theorem star_72_92 (h : Injective R) (hs : Subrelation S R) :
    S = RestrictRange R (Range S) := by
  funext x y; apply propext
  exact ⟨fun q => ⟨hs q, ⟨x, q⟩⟩, fun q => (star_72_9 h hs).mpr q⟩

def Disjoint (A B : Class α) : Prop := ∀ x, ¬ (A x ∧ B x)

theorem star_72_41 (h : Injective R) (hd : Disjoint A B) :
    Disjoint (Image R A) (Image R B) := by
  intro y
  rintro ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  have e : x = z := h hxy hzy
  exact hd x ⟨hxA, e ▸ hzB⟩

theorem star_72_411 (h : Functional R) (hd : Disjoint A B) :
    Disjoint (Preimage R A) (Preimage R B) := by
  intro x
  rintro ⟨⟨y, hyA, hxy⟩, ⟨z, hzB, hxz⟩⟩
  have e : y = z := h hxy hxz
  exact hd y ⟨hyA, e ▸ hzB⟩

theorem star_72_42 (h : Injective R) :
    (∃ y, Image R A y ∧ Image R B y) → ∃ x, A x ∧ B x := by
  rintro ⟨y, ⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  have e : x = z := h hxy hzy
  exact ⟨x, hxA, e ▸ hzB⟩

theorem star_72_421 (h : Functional R) :
    (∃ x, Preimage R A x ∧ Preimage R B x) → ∃ y, A y ∧ B y := by
  rintro ⟨x, ⟨y, hyA, hxy⟩, ⟨z, hzB, hxz⟩⟩
  have e : y = z := h hxy hxz
  exact ⟨y, hyA, e ▸ hzB⟩

theorem star_72_47 (h : Injective R) :
    Image R A = Range R ↔ Included (Domain R) A := by
  constructor
  · intro e x
    rintro ⟨y, hxy⟩
    have hi : Image R A y := e.symm ▸ ⟨x, hxy⟩
    rcases hi with ⟨z, hzA, hzy⟩
    exact h hxy hzy ▸ hzA
  · intro hi; funext y; apply propext
    exact ⟨fun ⟨x, _, hxy⟩ => ⟨x, hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x, hi ⟨y, hxy⟩, hxy⟩⟩

theorem star_72_471 (h : Functional R) :
    Preimage R B = Domain R ↔ Included (Range R) B := by
  constructor
  · intro e y
    rintro ⟨x, hxy⟩
    have hi : Preimage R B x := e.symm ▸ ⟨y, hxy⟩
    rcases hi with ⟨z, hzB, hxz⟩
    exact h hxy hxz ▸ hzB
  · intro hi; funext x; apply propext
    exact ⟨fun ⟨y, _, hxy⟩ => ⟨y, hxy⟩,
      fun ⟨y, hxy⟩ => ⟨y, hi ⟨x, hxy⟩, hxy⟩⟩

theorem star_72_48 (h : Injective R) (hA : Included A (Domain R))
    (hB : Included B (Domain R)) : Image R A = Image R B ↔ A = B := by
  exact ⟨star_72_44 h hA hB, fun e => e ▸ rfl⟩

theorem star_72_481 (h : Functional R) (hA : Included A (Range R))
    (hB : Included B (Range R)) : Preimage R A = Preimage R B ↔ A = B := by
  constructor
  · intro e
    have q : Inter A (Range R) = Inter B (Range R) := by
      rw [← star_72_501 h, ← star_72_501 h, e]
    funext y; apply propext
    exact ⟨fun hy => (congrFun q y |>.mp ⟨hy, hA hy⟩).1,
      fun hy => (congrFun q y |>.mpr ⟨hy, hB hy⟩).1⟩
  · rintro rfl; rfl

theorem star_72_51 (h : Injective R) (hA : Included A (Domain R)) :
    A = Preimage R (Image R A) := (star_72_502 h hA).symm

theorem star_72_511 (h : Functional R) (hB : Included B (Range R)) :
    B = Image R (Preimage R B) := (star_72_503 h hB).symm

theorem star_72_52 (h : OneOne R) (hA : Included A (Domain R))
    (hB : Included B (Range R)) :
    A = Preimage R B ↔ B = Image R A := by
  constructor
  · intro e; rw [e, star_72_503 h.1 hB]
  · intro e; rw [e, star_72_502 h.2 hA]

theorem star_72_53 (h : OneOne R) :
    (Included B (Range R) ∧ A = Preimage R B) ↔
      (Included A (Domain R) ∧ B = Image R A) := by
  constructor
  · rintro ⟨hB, rfl⟩
    refine ⟨fun _ ⟨y, _, hxy⟩ => ⟨y, hxy⟩, ?_⟩
    exact (star_72_503 h.1 hB).symm
  · rintro ⟨hA, rfl⟩
    refine ⟨fun _ ⟨x, _, hxy⟩ => ⟨x, hxy⟩, ?_⟩
    exact (star_72_502 h.2 hA).symm

theorem star_72_55 (R : Rel α α) (A : Class α) :
    RestrictRange R A = RestrictRange (RestrictRange R A) A := by
  funext x y; apply propext
  exact ⟨fun h => ⟨h, h.2⟩, fun h => h.1⟩

theorem star_72_551 (R : Rel α α) (A : Class α) :
    RestrictDomain R A = RestrictDomain (RestrictDomain R A) A := by
  funext x y; apply propext
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

theorem star_72_93 (h : Functional R) :
    Subrelation R S ↔ ∀ ⦃x y⦄, R x y → S x y := Iff.rfl

theorem star_72_94 (hR : Functional R) (hS : Functional S) :
    (∃ x y, R x y ∧ S x y) ↔ ∃ x, Range (fun z y => R z y ∧ S z y) x := by
  constructor
  · rintro ⟨x, y, hr, hs⟩; exact ⟨y, x, hr, hs⟩
  · rintro ⟨y, x, hr, hs⟩; exact ⟨x, y, hr, hs⟩

theorem star_72_54 (R : Rel α α) (A : Class α) :
    Converse (RestrictRange R A) = RestrictDomain (Converse R) A := by
  funext x y; apply propext
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem star_72_541 (R : Rel α α) (A B : Class α) :
    Converse (RestrictRange (RestrictDomain R A) B) =
      RestrictDomain (RestrictRange (Converse R) A) B := by
  funext x y; apply propext
  simp [Converse, RestrictRange, RestrictDomain, and_comm, and_left_comm, and_assoc]

theorem star_72_57 (R : Rel α α) (A : Class α) :
    Image (RestrictDomain R A) A = Image R A := by
  funext y; apply propext
  exact ⟨fun ⟨x, _, _, hxy⟩ => ⟨x, ‹A x›, hxy⟩,
    fun ⟨x, hx, hxy⟩ => ⟨x, hx, hx, hxy⟩⟩

theorem star_72_61 (hR : Injective R) (hS : Injective S) :
    Injective (Compose R S) := star_72_201 hR hS

theorem star_72_611 (hR : Functional R) (hS : Functional S) :
    Functional (Compose R S) := star_72_2 hR hS

theorem star_72_622 (h : Functional R) :
    Compose R (Converse R) x z ↔ x = z ∧ Range R x := star_72_591 h

theorem star_72_63 (h : Functional R) :
    (Compose R (Converse R) x z → x = z) :=
  fun q => (star_72_591 h).mp q |>.1

theorem star_72_64 (A : Class α) :
    OneOne (fun x y : α => A x ∧ y = x) := by
  constructor
  · rintro x y z ⟨_, rfl⟩ ⟨_, rfl⟩; rfl
  · rintro x z y ⟨_, rfl⟩ ⟨_, h⟩; exact h

theorem star_72_65 (R : Rel α α) :
    Converse (Converse R) = R := converse_converse R

theorem star_72_66 (h : OneOne R) :
    Converse (Compose (Converse R) R) = Compose (Converse R) R := by
  funext x z; apply propext; constructor
  · intro q
    have e := (star_72_59 h.2).mp q |>.1
    exact e ▸ q
  · intro q
    have e := (star_72_59 h.2).mp q |>.1
    exact e ▸ q

theorem star_72_8 (A : Class α) :
    Functional (fun x y : α => A x ∧ y = x) := by
  rintro x y z ⟨_, rfl⟩ ⟨_, rfl⟩; rfl

theorem star_72_81 (A : Class α) :
    Injective (fun x y : α => A y ∧ x = y) := by
  rintro x z y ⟨_, rfl⟩ ⟨_, rfl⟩; rfl

theorem star_72_911 (h : Functional R) (hs : Subrelation S R) :
    Domain (Difference R S) x ↔ Domain R x ∧ ¬ Domain S x := by
  constructor
  · rintro ⟨y, rxy, nsxy⟩; refine ⟨⟨y, rxy⟩, ?_⟩
    rintro ⟨z, sxz⟩
    have e : z = y := h (hs sxz) rxy
    exact nsxy (e ▸ sxz)
  · rintro ⟨⟨y, rxy⟩, hn⟩
    exact ⟨y, rxy, fun sxy => hn ⟨y, sxy⟩⟩

theorem star_72_921 (h : Functional R) (hs : Subrelation S R) :
    S = RestrictDomain R (Domain S) := by
  funext x y; apply propext; constructor
  · exact fun q => ⟨⟨y, q⟩, hs q⟩
  · rintro ⟨⟨z, sxz⟩, rxy⟩
    have e : z = y := h (hs sxz) rxy
    exact e ▸ sxz

theorem star_72_931 (h : Functional R) :
    Subrelation R S ↔ ∀ ⦃x y⦄, R x y → S x y := Iff.rfl

theorem star_72_941 (R S : Rel α α) :
    (∃ x y, R x y ∧ S x y) ↔ ∃ x y, S x y ∧ R x y := by
  constructor <;> rintro ⟨x, y, h₁, h₂⟩ <;> exact ⟨x, y, h₂, h₁⟩

theorem star_72_1 : OneOne (fun x y : α => False) := by
  exact ⟨fun _ _ _ h => False.elim h, fun _ _ _ h => False.elim h⟩

theorem star_72_11 : Functional (fun R S : Rel α α => S = Converse R) := by
  rintro R S T rfl h; exact h.symm

theorem star_72_12 (R : Rel α α) : Functional (fun x : α => fun A : Class α => A = fun y => R x y) := by
  rintro x A B rfl h; exact h.symm

theorem star_72_121 : OneOne (fun x : α => fun A : Class α => A = fun y => y = x) := by
  constructor
  · rintro x A B rfl h; exact h.symm
  · rintro x z A hx hz
    have q := congrFun (hx.symm.trans hz) x
    exact q.mp rfl

theorem star_72_13 : Functional (fun R : Rel α α => fun A : Rel α α => A = fun x _ => ∃ z, R x z) := by
  rintro R A B rfl h; exact h.symm

theorem star_72_131 : Functional (fun R : Rel α α => fun A : Rel α α => A = fun _ y => ∃ z, R z y) := by
  rintro R A B rfl h; exact h.symm

theorem star_72_132 : Functional (fun R A : Rel α α => A = Converse R) := by
  rintro R A B rfl h; exact h.symm

theorem star_72_14 (x : α) : Functional (fun y : α => fun A : Class α => A = fun z => z = x ∧ z = y) := by
  rintro y A B rfl h; exact h.symm

theorem star_72_15 : Functional (fun A R : Rel α α => R = fun x y => A x x ∧ x = y) := by
  rintro A R S rfl h; exact h.symm

theorem star_72_16 (p : Prop) : Functional (fun _ : Unit => fun A : Class α => A = fun _ => p) := by
  rintro _ A B hA hB; exact hA.trans hB.symm

theorem star_72_161 (A : Class α) : Functional (fun _ : Unit => fun B : Class α => B = A) := by
  rintro _ B C hB hC; exact hB.trans hC.symm

theorem star_72_162 (p : Prop) : Functional (fun _ : Unit => fun A : Class α => A = fun _ => p) := star_72_16 p

theorem star_72_163 (A : Class α) : Functional (fun _ : Unit => fun B : Class α => B = A) := star_72_161 A

theorem star_72_17 : OneOne (fun x y : α => x = y) := by
  constructor
  · rintro x y z rfl h; exact h
  · rintro x z y rfl h; exact h.symm

theorem star_72_18 : OneOne (fun x : α => fun A : Class α => A = fun y => y = x) := star_72_121

theorem star_72_181 : OneOne (fun A : Class α => fun x : α => A = fun y => y = x) := by
  constructor
  · rintro A x z hx hz
    have q := congrFun (hx.symm.trans hz) x
    exact q.mp rfl
  · rintro A B x rfl h; exact h.symm

theorem star_72_182 (x : α) : Functional (fun y z : α => z = x ∧ z = y) := by
  rintro y z w ⟨_, rfl⟩ ⟨_, h⟩; exact h.symm

theorem star_72_184 (x : α) : Functional (fun y z : α => y = x ∧ z = x) := by
  rintro y z w ⟨_, hz⟩ ⟨_, hw⟩; exact hz.trans hw.symm

theorem star_72_185 (x : α) : Functional (fun A : Class α => fun y : Class α => y = A) := by
  rintro A y z hA hB; exact hA.trans hB.symm

theorem star_72_19 : OneOne (fun A : Class α => fun B : Class (Class α) => B = fun C => C = A) := by
  constructor
  · rintro A B C rfl h; exact h.symm
  · rintro A B C hA hB
    have q := congrFun (hA.symm.trans hB) A
    exact q.mp rfl

theorem star_72_191 : OneOne (fun R : Rel α α => fun A : Class (Rel α α) => A = fun S => S = R) := by
  constructor
  · rintro R A B rfl h; exact h.symm
  · rintro R S A hR hS
    have q := congrFun (hR.symm.trans hS) R
    exact q.mp rfl

theorem star_72_192 : Functional (fun A : Class α => fun p : Prop => p = (∃ x, A x)) := by
  rintro A p q hp hq; exact hp.trans hq.symm

theorem star_72_193 : Functional (fun R : Rel α α => fun p : Prop => p = (∃ x y, R x y)) := by
  rintro R p q hp hq; exact hp.trans hq.symm

theorem star_72_22 (hR : Functional R) (hS : Functional S)
    (hx : Domain (Compose R S) x) :
    ∃ z, Compose R S x z := hx

theorem star_72_221 (hR : Injective R) (hS : Injective S)
    (hz : Range (Compose R S) z) :
    ∃ x, Compose R S x z := hz

theorem star_72_23 (A : Class α) :
    Image (Compose R S) A = Image R (Image S A) := by
  funext z; apply propext; constructor
  · rintro ⟨x, hxA, y, hs, hr⟩; exact ⟨y, ⟨x, hxA, hs⟩, hr⟩
  · rintro ⟨y, ⟨x, hxA, hs⟩, hr⟩; exact ⟨x, hxA, y, hs, hr⟩

theorem star_72_25 (h : OneOne R) (hy : Range R y) :
    Compose R (Converse R) y y := (star_72_241 h).mp hy

theorem star_72_26 (h : Functional R) :
    R = RestrictDomain R (Domain R) := by
  funext x y; apply propext
  exact ⟨fun q => ⟨⟨y, q⟩, q⟩, And.right⟩

theorem star_72_27 (R : Rel α α) (h : Functional R) :
    Domain R = Domain (RestrictDomain R (Domain R)) := by
  rw [← star_72_26 (R := R) h]

theorem star_72_3 (P : Class (Rel α α)) (h : Exists fun R => P R ∧ Functional R) :
    ∃ R, P R ∧ Functional R := by
  exact h

theorem star_72_301 (P : Class (Rel α α)) (h : Exists fun R => P R ∧ Injective R) :
    ∃ R, P R ∧ Injective R := by
  exact h

theorem star_72_302 (P : Class (Rel α α)) (h : Exists fun R => P R ∧ OneOne R) :
    ∃ R, P R ∧ OneOne R := by
  exact h

theorem star_72_31 (P : Class (Rel α α)) (R : Rel α α)
    (hR : P R ∧ Functional R) : P R := hR.1

theorem star_72_311 (P : Class (Rel α α)) (R : Rel α α)
    (hR : P R ∧ Injective R) : P R := hR.1

theorem star_72_312 (P : Class (Rel α α)) (R : Rel α α)
    (hR : P R ∧ OneOne R) : P R := hR.1

theorem star_72_303 (P : Class (Rel α α)) (h : Exists fun R => P R ∧ OneOne R) :
    ∃ R : Rel α α, OneOne R := by rcases h with ⟨R, _, hR⟩; exact ⟨R, hR⟩

theorem star_72_32 (P : Class (Rel α α)) (h : ∀ ⦃R S⦄, P R → P S → R = S)
    (R S : Rel α α) (hR : P R) (hS : P S) : R = S := h hR hS

theorem star_72_321 (P : Class (Rel α α)) (h : ∀ ⦃R S⦄, P R → P S → R = S) :
    ∀ ⦃R S⦄, P R → P S → R = S := h

theorem star_72_322 (P : Class (Rel α α)) (h : ∀ ⦃R S⦄, P R → P S → R = S)
    (R S : Rel α α) : P R → P S → R = S := fun a b => h a b

theorem star_72_323 (P : Class (Rel α α)) (h : ∀ ⦃R S⦄, P R → P S → R = S)
    (R S : Rel α α) (q : P R ∧ P S) : R = S := h q.1 q.2

theorem star_72_34 (h : Functional R) (A : Class α) :
    Image R A = fun y => ∃ x, A x ∧ R x y := rfl

theorem star_72_341 (h : Injective R) (A : Class α) :
    Preimage R A = fun x => ∃ y, A y ∧ R x y := rfl

theorem star_72_45 (h : Injective R) (A : Class α) :
    Included (Image R A) (Range R) := fun {_} ⟨x, _, hxy⟩ => ⟨x, hxy⟩

theorem star_72_451 (h : Functional R) (A : Class α) :
    Functional (fun B C : Class α => C = Preimage R (Inter A B)) := by
  rintro B C D rfl q; exact q.symm

theorem star_72_49 :
    Range (Compose R S) = Image R (Range S) := by
  funext y; apply propext; constructor
  · rintro ⟨x, z, hs, hr⟩; exact ⟨z, ⟨x, hs⟩, hr⟩
  · rintro ⟨z, ⟨x, hs⟩, hr⟩; exact ⟨x, z, hs, hr⟩

theorem star_72_491 (h : Functional R) :
    Domain (Compose R S) = Preimage S (Domain R) := by
  funext x; apply propext; constructor
  · rintro ⟨y, z, hs, hr⟩; exact ⟨z, ⟨y, hr⟩, hs⟩
  · rintro ⟨z, ⟨y, hr⟩, hs⟩; exact ⟨y, z, hs, hr⟩

theorem star_72_492 (hR : Functional R) (hS : Functional S) :
    Domain (Compose R S) = Preimage S (Domain R) ∧
      Range (Compose R S) = Image R (Range S) :=
  ⟨star_72_491 hR, star_72_49⟩

theorem star_72_504 (h : Injective R) (A : Class α) :
    Preimage R (Image R A) = Inter A (Domain R) := star_72_5 h

theorem star_72_513 (h : Functional R) (hB : Included B (Range R)) (hy : R x y) :
    (B y ↔ Preimage R B x) := star_72_512 h hB hy

theorem star_72_512b (h : Functional R) (hy : R x y) (hz : R x z) : y = z := h hy hz

theorem star_72_46b (h : Injective R) (A B : Class α) :
    Image R A = Image R B ↔ Inter A (Domain R) = Inter B (Domain R) := star_72_46 h

theorem star_72_461 (h : Functional R) (A B : Class α) :
    Preimage R A = Preimage R B ↔ Inter A (Range R) = Inter B (Range R) := by
  constructor
  · intro e; rw [← star_72_501 h, ← star_72_501 h, e]
  · intro e; funext x; apply propext; constructor
    · rintro ⟨y, hyA, hxy⟩
      have q := congrFun e y |>.mp ⟨hyA, ⟨x, hxy⟩⟩
      exact ⟨y, q.1, hxy⟩
    · rintro ⟨y, hyB, hxy⟩
      have q := congrFun e y |>.mpr ⟨hyB, ⟨x, hxy⟩⟩
      exact ⟨y, q.1, hxy⟩

theorem star_72_52b (h : OneOne R) (hA : Included A (Domain R))
    (hB : Included B (Range R)) : A = Preimage R B ↔ B = Image R A :=
  star_72_52 h hA hB

theorem star_72_53b (h : OneOne R) :
    (Included B (Range R) ∧ A = Preimage R B) ↔
      (Included A (Domain R) ∧ B = Image R A) := star_72_53 h

theorem star_72_59b (h : Injective R) :
    Compose (Converse R) R x z ↔ x = z ∧ Domain R x := star_72_59 h

theorem star_72_6b (h : Functional R) :
    Preimage R (Range R) = Domain R := by
  funext x; apply propext
  exact ⟨fun ⟨y, _, hxy⟩ => ⟨y, hxy⟩,
    fun ⟨y, hxy⟩ => ⟨y, ⟨x, hxy⟩, hxy⟩⟩

theorem star_72_601b (h : Injective R) :
    Image R (Domain R) = Range R := by
  funext y; apply propext
  exact ⟨fun ⟨x, _, hxy⟩ => ⟨x, hxy⟩,
    fun ⟨x, hxy⟩ => ⟨x, ⟨y, hxy⟩, hxy⟩⟩

theorem star_72_61b (hR : OneOne R) (hS : OneOne S) :
    OneOne (Compose R S) := star_72_202 hR hS

theorem star_72_611b (h : OneOne R) : OneOne (Converse R) :=
  (converse_oneOne R).mpr h

theorem star_72_62b (h : Injective R) :
    Converse (Compose (Converse R) R) = Compose (Converse R) R := by
  funext x z; apply propext; constructor
  · intro q; have e := (star_72_59 (R := R) h).mp q |>.1; exact e ▸ q
  · intro q; have e := (star_72_59 (R := R) h).mp q |>.1; exact e ▸ q

theorem star_72_63b (h : Functional R) :
    Converse (Compose R (Converse R)) = Compose R (Converse R) := by
  funext x z; apply propext; constructor
  · intro q; have e := (star_72_591 (R := R) h).mp q |>.1; exact e ▸ q
  · intro q; have e := (star_72_591 (R := R) h).mp q |>.1; exact e ▸ q

theorem star_72_64b (h : Injective R) :
    Compose (Converse R) R x z → x = z := fun q => (star_72_59 h).mp q |>.1

theorem star_72_65b (h : Functional R) :
    Compose R (Converse R) x z → x = z := fun q => (star_72_591 h).mp q |>.1

theorem star_72_66b (h : OneOne R) :
    Converse (Compose R (Converse R)) = Compose R (Converse R) := star_72_63b h.1

theorem star_72_7b (h : Functional R) (A : Class α) :
    Functional (RestrictDomain R A) := star_72_7 h A

theorem star_72_71b (h : Injective R) (A : Class α) :
    Injective (RestrictRange R A) := star_72_71 h A

theorem star_72_72b (h : OneOne R) (A B : Class α) :
    OneOne (RestrictRange (RestrictDomain R A) B) := star_72_72 h A B

theorem star_72_8b (A : Class α) :
    Functional (fun x y : α => A x ∧ y = x) := star_72_8 A

theorem star_72_81b (A : Class α) :
    Injective (fun x y : α => A y ∧ x = y) := star_72_81 A

theorem star_72_9b (h : Injective R) (hs : Subrelation S R) :
    S x y ↔ R x y ∧ Range S y := star_72_9 h hs

theorem star_72_91b (h : Injective R) (hs : Subrelation S R) :
    Range (Difference R S) y ↔ Range R y ∧ ¬ Range S y := star_72_91 h hs

theorem star_72_911b (h : Functional R) (hs : Subrelation S R) :
    Domain (Difference R S) x ↔ Domain R x ∧ ¬ Domain S x := star_72_911 h hs

theorem star_72_92b (h : Injective R) (hs : Subrelation S R) :
    S = RestrictRange R (Range S) := star_72_92 h hs

theorem star_72_921b (h : Functional R) (hs : Subrelation S R) :
    S = RestrictDomain R (Domain S) := star_72_921 h hs

theorem star_72_93b (h : Functional R) :
    Subrelation R S ↔ ∀ ⦃x y⦄, R x y → S x y := star_72_93 h

theorem star_72_931b (h : Functional R) :
    Subrelation R S ↔ ∀ ⦃x y⦄, R x y → S x y := star_72_931 h

theorem star_72_94b (hR : Functional R) (hS : Functional S) :
    (∃ x y, R x y ∧ S x y) ↔ ∃ x, Range (fun z y => R z y ∧ S z y) x :=
  star_72_94 hR hS

theorem star_72_241b (h : OneOne R) :
    Range R y ↔ Compose R (Converse R) y y := star_72_241 h

theorem star_72_242 (h : OneOne R) :
    Domain R x → Compose (Converse R) R x x := (star_72_24 h).mp

theorem star_72_243 (h : OneOne R) :
    Range R y → Compose R (Converse R) y y := (star_72_241 h).mp

end PM.Architecture.Star72Kernel
