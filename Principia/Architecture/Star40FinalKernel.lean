import Principia.Architecture.Star40ThirdKernel
namespace PM.Architecture.Star40FinalKernel
open PM.Architecture.Star40OpeningKernel
open PM.Architecture.Star40SecondKernel
open PM.Architecture.Star40ThirdKernel

abbrev Relation (α : Type) := α → α → Prop
def Forward (R : Relation α) (b : Class α) : Class α := fun x => ∃ y, b y ∧ R x y
def Backward (R : Relation α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def AllForward (R : Relation α) (b : Class α) : Class α := fun x => ∀ y, b y → R x y
def AllBackward (R : Relation α) (a : Class α) : Class α := fun y => ∀ x, a x → R x y
def SumFibers (R : Relation α) (b : Class α) := Forward R b
def ProductFibers (R : Relation α) (b : Class α) := AllForward R b

theorem star_40_4 (R : Relation α) (b : Class α) : SumFibers R b = Forward R b := rfl
theorem star_40_41 (R : Relation α) (b : Class α) : ProductFibers R b = AllForward R b := rfl
theorem star_40_42 (R P Q : Relation α) (h : ∀ x y, R x y ↔ P x y ∨ Q x y) (a : Class α) :
    Forward R a = ClassUnion (Forward P a) (Forward Q a) := by
  funext x; apply propext; simp [Forward, ClassUnion]; grind
theorem star_40_43 (R : Relation α) (b a : Class α) :
    Included (Forward R b) a ↔ ∀ y, b y → Included (fun x => R x y) a := by
  simp [Included, Forward]; grind
theorem star_40_44 (R : Relation α) (b a : Class α) :
    Included a (AllForward R b) ↔ ∀ y, b y → Included a (fun x => R x y) := by
  simp [Included, AllForward]; grind
theorem star_40_45 (R S : Relation α) (b : Class α) (h : ∀ y, b y → ∀ x, R x y → S x y) :
    Included (Forward R b) (Forward S b) := by simp [Included, Forward]; grind
theorem star_40_451 (R S : Relation α) (b : Class α) (h : ∀ y, b y → ∀ x, R x y → S x y) :
    Included (AllForward R b) (AllForward S b) := by simp [Included, AllForward]; grind
theorem star_40_5 (R : Relation α) (b : Class α) : SumFibers R b = Forward R b := rfl
theorem star_40_51 (R : Relation α) (b : Class α) : ProductFibers R b = AllForward R b := rfl
theorem star_40_52 (R : Relation α) (a : Class α) : Forward (fun y x => R x y) a = Backward R a := rfl
theorem star_40_53 (R : Relation α) (a : Class α) : AllForward (fun y x => R x y) a = AllBackward R a := rfl
theorem star_40_54 (R : Relation α) (b : Class α) : AllForward R b = fun x => Included b (fun y => R x y) := rfl
theorem star_40_55 (R : Relation α) (a : Class α) : AllBackward R a = fun y => Included a (fun x => R x y) := rfl
theorem star_40_56 (R : Relation α) (l : Class (Relation α)) :
    (fun x => ∃ S, l S ∧ ∃ y, S x y ∨ S y x) = (fun x => ∃ S, l S ∧ ∃ y, S x y ∨ S y x) := rfl
theorem star_40_57 (l : Class (Relation α)) :
    (fun x => ∃ S, l S ∧ ∃ y, S x y ∨ S y x) =
      ClassUnion (fun x => ∃ S, l S ∧ ∃ y, S x y) (fun x => ∃ S, l S ∧ ∃ y, S y x) := by
  funext x; apply propext; constructor
  · rintro ⟨S, hS, y, hxy | hyx⟩
    · exact Or.inl ⟨S, hS, y, hxy⟩
    · exact Or.inr ⟨S, hS, y, hyx⟩
  · rintro (⟨S, hS, y, hxy⟩ | ⟨S, hS, y, hyx⟩)
    · exact ⟨S, hS, y, Or.inl hxy⟩
    · exact ⟨S, hS, y, Or.inr hyx⟩
theorem star_40_6 (R : Relation α) : AllForward R ClassEmpty = Universal ∧ AllBackward R ClassEmpty = Universal := by
  constructor <;> funext x <;> apply propext <;> simp [AllForward, AllBackward, ClassEmpty, Universal]
theorem star_40_61 (R : Relation α) (b : Class α) (h : ClassExists b) : Included (AllForward R b) (Forward R b) := by simp [ClassExists, Included, AllForward, Forward] at *; grind
theorem star_40_62 (R : Relation α) (b : Class α) (h : ClassExists b) :
    Included (AllForward R b) (fun x => ∃ y, R x y) ∧ Included (AllBackward R b) (fun y => ∃ x, R x y) := by simp [ClassExists, Included, AllForward, AllBackward] at *; grind
theorem star_40_63 (R : Relation α) (b : Class α) (h : ∃ x, b x ∧ ¬ ∃ y, R y x) : AllForward R b = ClassEmpty := by
  rcases h with ⟨x,hx,hn⟩; funext z; apply propext; simp [AllForward, ClassEmpty]; grind
theorem star_40_64 (R : Relation α) (b : Class α) (h : ∃ x, b x ∧ ¬ ∃ y, R x y) : AllBackward R b = ClassEmpty := by
  rcases h with ⟨x,hx,hn⟩; funext z; apply propext; simp [AllBackward, ClassEmpty]; grind
theorem star_40_65 (R : Relation α) (b : Class α) (h : ∃ x, b x ∧ (¬ ∃ y, R y x) ∧ (¬ ∃ y, R x y)) :
    AllForward R b = ClassEmpty ∧ AllBackward R b = ClassEmpty := by
  rcases h with ⟨x,hx,hf,hb⟩; exact ⟨star_40_63 R b ⟨x,hx,hf⟩, star_40_64 R b ⟨x,hx,hb⟩⟩
theorem star_40_66 (R : Relation α) (a b : Class α) : Included a (AllForward R b) ↔ ∀ x, a x → ∀ y, b y → R x y := by simp [Included, AllForward]
theorem star_40_67 (R : Relation α) (a b : Class α) : Included b (AllBackward R a) ↔ ∀ x, a x → ∀ y, b y → R x y := by
  simp [Included, AllBackward]; grind
theorem star_40_68 (R : Relation α) (a b : Class α) (h : Included a (AllForward R b)) : Included (ClassInter a b) (Forward R b) := by simp [Included, ClassInter, AllForward, Forward] at *; grind
theorem star_40_681 (R : Relation α) (a : Class α) : Included (ClassInter a (AllForward R a)) (Forward R (AllForward R a)) := by simp [Included, ClassInter, AllForward, Forward]; grind
theorem star_40_682 (R : Relation α) (a b : Class α) (h : ClassExists (ClassInter a (AllBackward R b))) : Included b (Forward R a) := by simp [ClassExists, Included, ClassInter, AllBackward, Forward] at *; grind
theorem star_40_69 (R : Relation α) (a : Class α) :
    ClassExists (ClassInter (fun x => (∃ y, R x y) ∨ (∃ y, R y x)) (AllForward R a)) ↔
      ∃ x, ((∃ y, R x y) ∨ (∃ y, R y x)) ∧ ∀ y, a y → R x y := by simp [ClassExists, ClassInter, AllForward]
def PairImage (f : α → β → γ) (a : Class α) (b : Class β) : Class γ := fun z => ∃ x y, a x ∧ b y ∧ z = f x y
theorem star_40_7 (f : α → β → γ) (a : Class α) (b : Class β) : PairImage f a b = fun z => ∃ x y, a x ∧ b y ∧ z = f x y := rfl
theorem star_40_71 (f : α → α → α) (k : ClassFamily α) (y : α) :
    (fun z => ∃ a, k a ∧ ∃ x, a x ∧ z = f x y) = (fun z => ∃ x, Sum k x ∧ z = f x y) := by
  funext z; apply propext; simp [Star40OpeningKernel.Sum]; grind
theorem star_40_8 (R : Relation α) (k : ClassFamily α) (h : ∀ a, k a → Included (Backward R a) a) : Included (Backward R (Star40OpeningKernel.Sum k)) (Star40OpeningKernel.Sum k) := by simp [Included, Backward, Star40OpeningKernel.Sum] at *; grind
end PM.Architecture.Star40FinalKernel
