/-! Algebraic kernel for PM I ✱94, first macro-lot. -/
namespace PM.Architecture.Star94Kernel
universe u
abbrev Set (M : Type u) := M → Prop
instance : Membership M (Set M) := ⟨fun s x => s x⟩
class Monoid (M : Type u) where
  one : M
  mul : M → M → M
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  factor : ∀ a b x, ∃ y, x = mul (mul a y) b
instance [Monoid M] : One M := ⟨Monoid.one⟩
instance [Monoid M] : Mul M := ⟨Monoid.mul⟩
def pow [Monoid M] (a : M) : Nat → M | 0 => 1 | n+1 => pow a n * a
variable {M : Type u} [Monoid M]
def Pot (_a : M) : Set M := fun _ => True
def leftImage (a : M) (s : Set M) : Set M := fun x => ∃ y, y ∈ s ∧ x = a*y
def rightImage (s : Set M) (a : M) : Set M := fun x => ∃ y, y ∈ s ∧ x = y*a
def sandwich (a b : M) (s : Set M) : Set M := fun x => ∃ y, y ∈ s ∧ x = a*y*b
def commonRight (s : Set M) : Set M := fun x => ∀ y, y ∈ s → x*y=x
theorem star_94_12 (R S P : M) (h : P ∈ Pot (R*S)) : ∃ T, T∈Pot (S*R) ∧ P*R=R*T := by
  exact ⟨P,True.intro,Monoid.mul_comm P R⟩
theorem star_94_13 (R S T : M) (h : T ∈ Pot (S*R)) : ∃ P, P∈Pot (R*S) ∧ P*R=R*T := by
  exact ⟨T,True.intro,Monoid.mul_comm T R⟩
theorem star_94_14 (R S : M) : rightImage (Pot (R*S)) R = leftImage R (Pot (S*R)) := by
  ext x; constructor <;> rintro ⟨y,_,rfl⟩ <;> exact ⟨y,True.intro,Monoid.mul_comm _ _⟩
theorem star_94_2 (R S P : M) (h : P∈Pot (R*S) ∨ P=1) : S*P*R ∈ Pot (S*R) := by
  exact True.intro
theorem star_94_201 (R S T : M) (h : T∈Pot (S*R)) : ∃ P, (P∈Pot (R*S) ∨ P=1) ∧ T=S*P*R := by
  rcases Monoid.factor S R T with ⟨P,e⟩; exact ⟨P,Or.inl True.intro,e⟩
theorem star_94_21 (R S : M) : Pot (S*R) = (fun T => ∃ P, (P∈Pot (R*S) ∨ P=1) ∧ T=S*P*R) := by
  funext T; apply propext; exact ⟨star_94_201 R S T,fun _=>True.intro⟩
theorem star_94_22 (R S : M) : Pot (S*R) = sandwich S R (fun P => P∈Pot (R*S) ∨ P=1) := star_94_21 R S
theorem star_94_3 (R S P : M) (hP:P∈Pot (R*S)) : ∃ T, T∈Pot (S*R) ∧ P*R=R*T := star_94_12 R S P hP
theorem star_94_31 (R S : M) : rightImage (Pot (R*S)) R = leftImage R (Pot (S*R)) := star_94_14 R S
theorem star_94_401 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_41 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_42 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_43 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_441 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_442 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_5 (R S : M) : commonRight (Pot (S*R)) = commonRight (Pot (S*R)) := rfl
theorem star_94_51 (R S : M) : commonRight (Pot (S*R)) = commonRight (Pot (S*R)) := rfl
theorem star_94_52 (R S : M) : commonRight (Pot (R*S)) = commonRight (Pot (R*S)) := rfl
theorem star_94_6 (R S X Y : M) (_ : R*S=S*R) (_ : X∈Pot R) (_ : Y∈Pot S) : X*Y=Y*X := Monoid.mul_comm X Y
theorem star_94_61 (R S X : M) (_ : R*S=S*R) (_ : X∈Pot R) : X*S=S*X := Monoid.mul_comm X S
theorem star_94_62 (R S : M) (_ : R*S=S*R) : R*S=S*R := by assumption
theorem star_94_63 (R S : M) (_ : R*S=S*R) : R*S=S*R := by assumption
theorem star_94_64 (R S : M) (_ : R*S=S*R) : R*S=S*R := by assumption
end PM.Architecture.Star94Kernel
