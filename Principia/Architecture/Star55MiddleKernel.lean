import Principia.Architecture.Star55NextKernel
namespace PM.Architecture.Star55MiddleKernel
open PM.Architecture.Star55OpeningKernel PM.Architecture.Star55NextKernel

def mapClass (f : α→β) (A : Class α) : Class β := fun b=>∃a,A a∧f a=b
def Included (R S : Rel α) := ∀x y,R x y→S x y
def Inter (R S : Rel α) : Rel α := fun x y=>R x y∧S x y
def EmptyRel : Rel α := fun _ _=>False

private theorem class_ext {A B : Class α} (h:∀x,A x↔B x) : A=B := by funext x; exact propext (h x)
private theorem rel_ext {R S : Rel α} (h:∀x y,R x y↔S x y) : R=S := by funext x y; exact propext (h x y)

theorem star_55_26 (x : α) (A : Class α) :
    mapClass codomain (leftImage x A) = mapClass singleton A := by
  apply class_ext; intro B; constructor
  · rintro ⟨R,⟨y,hy,rfl⟩,rfl⟩; exact ⟨y,hy,(star_55_15 x y).2.1.symm⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨pair x y,⟨y,hy,rfl⟩,(star_55_15 x y).2.1⟩
theorem star_55_261 (x : α) (A : Class α) :
    mapClass domain (rightImage x A) = mapClass singleton A := by
  apply class_ext; intro B; constructor
  · rintro ⟨R,⟨y,hy,rfl⟩,rfl⟩; exact ⟨y,hy,(star_55_15 y x).1.symm⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨pair y x,⟨y,hy,rfl⟩,(star_55_15 y x).1⟩
theorem star_55_262 (x y : α) (A B : Class α) : rightImage x A=rightImage y B → A=B := by
  intro h; apply class_ext; intro z; constructor
  · intro hz; have q : rightImage y B (pair z x) := by rw [←h]; exact ⟨z,hz,rfl⟩
    rcases q with ⟨w,hw,he⟩; have e := (star_55_202 w y z x).mp he.symm
    exact e.1 ▸ hw
  · intro hz; have q : rightImage x A (pair z y) := by rw [h]; exact ⟨z,hz,rfl⟩
    rcases q with ⟨w,hw,he⟩; have e := (star_55_202 w x z y).mp he.symm
    exact e.1 ▸ hw
theorem star_55_27 (x : α) (A : Class α) :
    mapClass field (leftImage x A) = fun B=>∃y,A y∧B=(fun z=>z=x∨z=y) := by
  apply class_ext; intro B; constructor
  · rintro ⟨R,⟨y,hy,rfl⟩,rfl⟩; exact ⟨y,hy,(star_55_15 x y).2.2⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨pair x y,⟨y,hy,rfl⟩,(star_55_15 x y).2.2⟩
theorem star_55_28 (x y z : α) : codomain (pair x y)=codomain (pair x z) ↔ y=z := by
  rw [(star_55_15 x y).2.1,(star_55_15 x z).2.1]
  constructor
  · intro h
    have q : singleton z y := by rw [←h]; rfl
    change y=z at q; exact q
  · rintro rfl; rfl
theorem star_55_281 (x y z : α) : domain (pair y x)=domain (pair z x) ↔ y=z := by
  rw [(star_55_15 y x).1,(star_55_15 z x).1]
  constructor
  · intro h
    have q : singleton z y := by rw [←h]; rfl
    change y=z at q; exact q
  · rintro rfl; rfl
theorem star_55_282 (x y z : α) : field (pair x y)=field (pair x z) ↔ y=z := by
  rw [(star_55_15 x y).2.2,(star_55_15 x z).2.2]
  constructor
  · intro h
    have q : z=x∨z=y := by simpa using (congrFun h z).mpr (Or.inr rfl)
    rcases q with hzx|hzy
    · subst z
      have q2 : y=x∨y=x := by simpa using (congrFun h y).mp (Or.inr rfl)
      exact q2.elim id id
    · exact hzy.symm
  · rintro rfl; rfl
theorem star_55_283 (x y z : α) : field (pair y x)=field (pair z x) ↔ y=z := by
  rw [(star_55_15 y x).2.2,(star_55_15 z x).2.2]
  constructor
  · intro h
    have q : y=z∨y=x := by simpa using (congrFun h y).mp (Or.inl rfl)
    rcases q with hyz|hyx; exact hyz
    have q2 : z=y∨z=x := by simpa using (congrFun h z).mpr (Or.inl rfl)
    exact q2.elim (fun e=>e.symm) (fun e=>hyx.trans e.symm)
  · rintro rfl; rfl
theorem star_55_29 (x : α) : (fun y=>codomain (pair x y))=singleton := by funext y; exact (star_55_15 x y).2.1
theorem star_55_291 (x : α) : (fun y=>domain (pair y x))=singleton := by funext y; exact (star_55_15 y x).1
theorem star_55_292 (x : α) :
    (fun y=>field (pair x y))=(fun y z=>z=x∨z=y) := by funext y; exact (star_55_15 x y).2.2
theorem star_55_3 (R : Rel α) (x y : α) : R x y ↔ Included (pair x y) R := by
  constructor
  · intro h a b hab; rcases hab with ⟨rfl,rfl⟩; exact h
  · intro h; exact h x y ⟨rfl,rfl⟩
theorem star_55_31 (x y z w : α) : pair x y=pair z w ↔ pair x y z w := by
  rw [star_55_202]
  change (x=z ∧ y=w) ↔ (z=x ∧ w=y)
  constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
theorem star_55_32 (x y z w : α) : Inter (pair x y) (pair z w)=EmptyRel ↔ x≠z∨y≠w := by
  classical
  constructor
  · intro h
    by_cases hx:x=z; right; intro hy; subst z; subst w
    have q : Inter (pair x y) (pair x y) x y := ⟨⟨rfl,rfl⟩,rfl,rfl⟩
    rw [h] at q
    exact q
    left; exact hx
  · intro h; apply rel_ext; intro a b; constructor
    · rintro ⟨⟨hax,hby⟩,haz,hbw⟩; rcases h with hx|hy; exact (hx (hax.symm.trans haz)).elim; exact (hy (hby.symm.trans hbw)).elim
    · exact False.elim
theorem star_55_33 (R : Rel α) (x y : α) : R x y ↔ Inter (pair x y) R=pair x y := by
  constructor
  · intro h; apply rel_ext; intro a b; constructor
    · exact And.left
    · rintro ⟨rfl,rfl⟩; exact ⟨⟨rfl,rfl⟩,h⟩
  · intro h
    have q : Inter (pair x y) R x y := by rw [h]; exact ⟨rfl,rfl⟩
    exact q.2
end PM.Architecture.Star55MiddleKernel
