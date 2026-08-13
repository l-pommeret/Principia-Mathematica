import Principia.Architecture.Star55OpeningKernel
namespace PM.Architecture.Star55NextKernel
open PM.Architecture.Star55OpeningKernel

def leftFamily (x : α) : Rel α → Prop := fun R => ∃ y, R=pair x y
def rightFamily (x : α) : Rel α → Prop := fun R => ∃ y, R=pair y x
def leftImage (x : α) (A : Class α) : Rel α → Prop := fun R => ∃ y, A y ∧ R=pair x y
def rightImage (x : α) (A : Class α) : Rel α → Prop := fun R => ∃ y, A y ∧ R=pair y x
def SingletonClass (A : Class α) := ∃ x, A=singleton x

private theorem class_ext {A B : Class α} (h:∀x,A x↔B x) : A=B := by funext x; exact propext (h x)
private theorem relClass_ext {A B : Rel α → Prop} (h:∀R,A R↔B R) : A=B := by funext R; exact propext (h R)

theorem star_55_202 (x y z w : α) :
    pair x y=pair z w ↔ (x=z ∧ y=w) := by
  constructor
  · intro h
    have q : pair z w x y := by rw [←h]; exact ⟨rfl,rfl⟩
    exact q
  · rintro ⟨rfl,rfl⟩; rfl

theorem star_55_21 (x : α) :
    (∀ y, ∃ R, R=pair x y) ∧ (∀ y, ∃ R, R=pair y x) :=
  ⟨fun y=>⟨pair x y,rfl⟩,fun y=>⟨pair y x,rfl⟩⟩
theorem star_55_22 (x : α) : leftFamily x = fun R => ∃ y, R=pair x y := rfl
theorem star_55_221 (x : α) : rightFamily x = fun R => ∃ y, R=pair y x := rfl
theorem star_55_222 (R : Rel α) (x : α) (hu:∃a b,R=pair a b) :
    leftFamily x R ↔ domain R=singleton x ∧ SingletonClass (codomain R) := by
  rcases hu with ⟨a,b,rfl⟩
  constructor
  · rintro ⟨y,h⟩
    rw [h]
    exact ⟨(star_55_15 x y).1,y,(star_55_15 x y).2.1⟩
  · rintro ⟨hd,_⟩
    have ha : a=x := by
      have q : singleton x a := by rw [←hd]; exact ⟨b,rfl,rfl⟩
      change a=x at q; exact q
    subst a; exact ⟨b,rfl⟩
theorem star_55_223 (R : Rel α) (x : α) (hu:∃a b,R=pair a b) :
    rightFamily x R ↔ codomain R=singleton x ∧ SingletonClass (domain R) := by
  rcases hu with ⟨a,b,rfl⟩
  constructor
  · rintro ⟨y,h⟩
    rw [h]
    exact ⟨(star_55_15 y x).2.1,y,(star_55_15 y x).1⟩
  · rintro ⟨hc,_⟩
    have hb : b=x := by
      have q : singleton x b := by rw [←hc]; exact ⟨a,rfl,rfl⟩
      change b=x at q; exact q
    subst b; exact ⟨a,rfl⟩
theorem star_55_224 (x y : α) :
    (fun R => leftFamily x R ∧ rightFamily y R) = fun R => R=pair x y := by
  apply relClass_ext; intro R; constructor
  · rintro ⟨⟨a,ha⟩,b,hb⟩
    have e : pair x a = pair b y := ha.symm.trans hb
    rcases (star_55_202 x a b y).mp e with ⟨rfl,rfl⟩
    exact ha
  · rintro rfl; exact ⟨⟨y,rfl⟩,x,rfl⟩
theorem star_55_23 (x : α) (A : Class α) : leftImage x A = fun R=>∃y,A y∧R=pair x y := rfl
theorem star_55_231 (x : α) (A : Class α) : rightImage x A = fun R=>∃y,A y∧R=pair y x := rfl

def HasUnique {γ : Sort u} (A : γ→Prop) := ∃ x, A x ∧ ∀y,A y→y=x
theorem star_55_232 (x y : α) (A B : Class α) :
    HasUnique (fun R => rightImage x A R ∧ rightImage y B R) ↔ x=y ∧ HasUnique (fun z=>A z∧B z) := by
  constructor
  · rintro ⟨R,⟨⟨a,ha,hRa⟩,b,hb,hRb⟩,huniq⟩
    subst R; rcases (star_55_202 a x b y).mp hRb with ⟨rfl,rfl⟩
    refine ⟨rfl,a,⟨ha,hb⟩,?_⟩
    intro z hz
    have heq := huniq (pair z x) ⟨⟨z,hz.1,rfl⟩,z,hz.2,rfl⟩
    have := (star_55_202 z x a x).mp heq
    exact this.1
  · rintro ⟨rfl,a,⟨ha,hb⟩,hu⟩
    refine ⟨pair a x,⟨⟨a,ha,rfl⟩,a,hb,rfl⟩,?_⟩
    rintro R ⟨⟨z,hz,rfl⟩,w,hw,he⟩
    rcases (star_55_202 z x w x).mp he with ⟨hzw,_⟩; subst w
    rw [hu z ⟨hz,hw⟩]
theorem star_55_233 (x y : α) (A B : Class α) (h:x≠y) :
    ¬ HasUnique (fun R => rightImage x A R ∧ rightImage y B R) := fun q=>h ((star_55_232 x y A B).mp q).1
theorem star_55_24 (x : α) (A : Class α) : leftImage x A = fun R=>∃y,A y∧R=pair x y := rfl
theorem star_55_241 (x : α) (A : Class α) : rightImage x A = fun R=>∃y,A y∧R=pair y x := rfl
theorem star_55_25 (x : α) (A : Class α) (h:HasUnique A) :
    (fun D => ∃ R, leftImage x A R ∧ D=domain R) = fun D=>D=singleton x := by
  apply class_ext; intro D; constructor
  · rintro ⟨R,⟨y,_,rfl⟩,rfl⟩; exact (star_55_15 x y).1
  · intro hD; rcases h with ⟨y,hy,_⟩; exact ⟨pair x y,⟨y,hy,rfl⟩,hD.trans (star_55_15 x y).1.symm⟩
theorem star_55_251 (x : α) (A : Class α) (h:HasUnique A) :
    (fun D => ∃ R, rightImage x A R ∧ D=codomain R) = fun D=>D=singleton x := by
  apply class_ext; intro D; constructor
  · rintro ⟨R,⟨y,_,rfl⟩,rfl⟩; exact (star_55_15 y x).2.1
  · intro hD; rcases h with ⟨y,hy,_⟩; exact ⟨pair y x,⟨y,hy,rfl⟩,hD.trans (star_55_15 y x).2.1.symm⟩
end PM.Architecture.Star55NextKernel
