namespace PM.Architecture.Star35CompositionKernel

universe u v w

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def leftRestriction (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y

def rightRestriction (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y

def bothRestrictions (a : Class α) (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => a x ∧ R x y ∧ b y

def classIntersection (a b : Class α) : Class α := fun x => a x ∧ b x

def composition (R : Relation α β) (S : Relation β γ) : Relation α γ :=
  fun x z => ∃ y, R x y ∧ S y z

/-- The bracket convention introduced by PM I ✱35·24. -/
def leftRestrictedComposition (a : Class α) (R : Relation α β)
    (S : Relation β γ) : Relation α γ := composition (leftRestriction a R) S

/-- The bracket convention introduced by PM I ✱35·25. -/
def rightRestrictedComposition (S : Relation α β) (R : Relation β γ)
    (c : Class γ) : Relation α γ := rightRestriction (composition S R) c

/-- The bracket convention introduced by PM I ✱35·27. -/
def restrictedComposition (a : Class α) (R : Relation α β)
    (S : Relation β γ) (c : Class γ) : Relation α γ :=
  rightRestriction (leftRestrictedComposition a R S) c

/-- PM I ✱35·21, retaining both printed equalities. -/
theorem star_35_21 (a : Class α) (R : Relation α β) (b : Class β) :
    bothRestrictions a R b = rightRestriction (leftRestriction a R) b ∧
      rightRestriction (leftRestriction a R) b = leftRestriction a (rightRestriction R b) := by
  constructor <;> funext x y <;> apply propext <;>
    simp [bothRestrictions, leftRestriction, rightRestriction, and_assoc]

/-- PM I ✱35·22. -/
theorem star_35_22 (a : Class α) (R : Relation α β) (S : Relation β γ) :
    composition (leftRestriction a R) S = leftRestriction a (composition R S) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨hax, hxy⟩, hyz⟩
    exact ⟨hax, ⟨y, hxy, hyz⟩⟩
  · rintro ⟨hax, ⟨y, hxy, hyz⟩⟩
    exact ⟨y, ⟨hax, hxy⟩, hyz⟩

/-- PM I ✱35·23. -/
theorem star_35_23 (S : Relation α β) (R : Relation β γ) (c : Class γ) :
    composition S (rightRestriction R c) = rightRestriction (composition S R) c := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz, hcz⟩
    exact ⟨⟨y, hxy, hyz⟩, hcz⟩
  · rintro ⟨⟨y, hxy, hyz⟩, hcz⟩
    exact ⟨y, hxy, hyz, hcz⟩

/-- PM I ✱35·24: the bracket convention is an eliminable abbreviation. -/
def star_35_24 (a : Class α) (R : Relation α β)
    (S : Relation β γ) : Relation α γ :=
  composition (leftRestriction a R) S

/-- PM I ✱35·25: the bracket convention is an eliminable abbreviation. -/
def star_35_25 (S : Relation α β) (R : Relation β γ)
    (c : Class γ) : Relation α γ :=
  rightRestriction (composition S R) c

theorem star_35_24_unfold (a : Class α) (R : Relation α β)
    (S : Relation β γ) :
    star_35_24 a R S = composition (leftRestriction a R) S := rfl

theorem star_35_25_unfold (S : Relation α β) (R : Relation β γ)
    (c : Class γ) :
    star_35_25 S R c = rightRestriction (composition S R) c := rfl

/-- PM I ✱35·26, retaining its eight printed forms. -/
theorem star_35_26 (a : Class α) (R : Relation α β) (S : Relation β γ) (c : Class γ) :
    composition (leftRestriction a R) (rightRestriction S c) =
        bothRestrictions a (composition R S) c ∧
    bothRestrictions a (composition R S) c =
        rightRestriction (leftRestriction a (composition R S)) c ∧
    rightRestriction (leftRestriction a (composition R S)) c =
        leftRestriction a (rightRestriction (composition R S) c) ∧
    leftRestriction a (rightRestriction (composition R S) c) =
        rightRestriction (composition (leftRestriction a R) S) c ∧
    rightRestriction (composition (leftRestriction a R) S) c =
        leftRestriction a (composition R (rightRestriction S c)) ∧
    leftRestriction a (composition R (rightRestriction S c)) =
        restrictedComposition a R S c ∧
    restrictedComposition a R S c =
        leftRestriction a (rightRestrictedComposition R S c) := by
  have hAB : composition (leftRestriction a R) (rightRestriction S c) =
      bothRestrictions a (composition R S) c := by
    funext x z
    apply propext
    constructor
    · rintro ⟨y, ⟨hax, hxy⟩, hyz, hcz⟩
      exact ⟨hax, ⟨y, hxy, hyz⟩, hcz⟩
    · rintro ⟨hax, ⟨y, hxy, hyz⟩, hcz⟩
      exact ⟨y, ⟨hax, hxy⟩, hyz, hcz⟩
  have hBC := (star_35_21 a (composition R S) c).1
  have hCD := (star_35_21 a (composition R S) c).2
  have hCE : rightRestriction (leftRestriction a (composition R S)) c =
      rightRestriction (composition (leftRestriction a R) S) c :=
    congrArg (fun T => rightRestriction T c) (star_35_22 a R S).symm
  have hDF : leftRestriction a (rightRestriction (composition R S) c) =
      leftRestriction a (composition R (rightRestriction S c)) :=
    congrArg (fun T => leftRestriction a T) (star_35_23 R S c).symm
  have hDE := hCD.symm.trans hCE
  have hEF := hDE.symm.trans hDF
  refine ⟨hAB, hBC, hCD, hDE, hEF, ?_, ?_⟩
  · simpa [restrictedComposition, leftRestrictedComposition] using hEF.symm
  · simpa [restrictedComposition, leftRestrictedComposition, rightRestrictedComposition]
      using hDE.symm

/-- PM I ✱35·27: the bracket convention is an eliminable abbreviation. -/
def star_35_27 (a : Class α) (R : Relation α β)
    (S : Relation β γ) (c : Class γ) : Relation α γ :=
  rightRestriction (leftRestrictedComposition a R S) c

theorem star_35_27_unfold (a : Class α) (R : Relation α β)
    (S : Relation β γ) (c : Class γ) :
    star_35_27 a R S c = rightRestriction (leftRestrictedComposition a R S) c := rfl

/-- PM I ✱35·31. -/
theorem star_35_31 (R : Relation α β) (a b : Class β) :
    rightRestriction (rightRestriction R a) b =
      rightRestriction R (classIntersection a b) := by
  funext x y
  apply propext
  simp [rightRestriction, classIntersection, and_assoc]

end PM.Architecture.Star35CompositionKernel
