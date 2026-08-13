import Principia.Architecture.Star55MiddleKernel
namespace PM.Architecture.Star55FiniteKernel
open PM.Architecture.Star55OpeningKernel PM.Architecture.Star55MiddleKernel PM.Architecture.Star55NextKernel
def Union (R S : Rel α) : Rel α := fun x y=>R x y∨S x y
def Diff (R S : Rel α) : Rel α := fun x y=>R x y∧¬S x y
def Identity : Rel α := fun x y=>x=y
def Diversity : Rel α := fun x y=>x≠y
private theorem rel_ext {R S : Rel α} (h:∀x y,R x y↔S x y):R=S:=by funext x y; exact propext (h x y)

theorem star_55_34 (R : Rel α) (x y : α) : Included R (pair x y) ∧ (∃a b,R a b) → R=pair x y := by
  rintro ⟨hs,a,b,hab⟩; have e:=hs a b hab
  apply rel_ext; intro u v; constructor
  · exact hs u v
  · rintro ⟨rfl,rfl⟩; rcases e with ⟨rfl,rfl⟩; exact hab
theorem star_55_341 (R : Rel α) (x y : α) : Included R (pair x y) ↔ R=EmptyRel∨R=pair x y := by
  constructor
  · intro h; by_cases hn:∃a b,R a b; exact Or.inr (star_55_34 R x y ⟨h,hn⟩)
    left; apply rel_ext; intro a b; exact ⟨fun q=>(hn ⟨a,b,q⟩).elim,False.elim⟩
  · rintro (rfl|rfl); intro a b h; exact h.elim; exact fun _ _ h=>h
theorem star_55_35 (R S : Rel α) (x y : α)
    (hd:Inter R (pair x y)=EmptyRel) (hu:Union R (pair x y)=S) :
    S x y ∧ R=Diff S (pair x y) := by
  constructor
  · rw [←hu]; exact Or.inr ⟨rfl,rfl⟩
  · apply rel_ext; intro a b; constructor
    · intro hr; refine ⟨by rw [←hu]; exact Or.inl hr,?_⟩
      intro hp; have q:Inter R (pair x y) a b:=⟨hr,hp⟩; rw [hd] at q; exact q
    · rintro ⟨hs,hn⟩; rw [←hu] at hs; exact hs.resolve_right hn
theorem star_55_36 (R : Rel α) (x y : α) : R x y ↔ Union (Diff R (pair x y)) (pair x y)=R := by
  constructor
  · intro h; apply rel_ext; intro a b; constructor
    · rintro (⟨q,_⟩|⟨rfl,rfl⟩); exact q; exact h
    · intro q; by_cases hp:pair x y a b; exact Or.inr hp; exact Or.inl ⟨q,hp⟩
  · intro h; have q:Union (Diff R (pair x y)) (pair x y) x y:=Or.inr ⟨rfl,rfl⟩; rwa [h] at q
theorem star_55_37 (A B : Class α) (x y : α) : A x∧B y ↔ Included (pair x y) (cross A B) := by
  constructor
  · rintro ⟨hx,hy⟩ a b ⟨rfl,rfl⟩; exact ⟨hx,hy⟩
  · intro h; exact h x y ⟨rfl,rfl⟩
theorem star_55_4 (x y z w a b : α) : Union (pair x y) (pair z w) a b ↔ (a=x∧b=y)∨(a=z∧b=w) := Iff.rfl
theorem star_55_41 (φ:α→α→Prop) (x y z w:α)
    (h:∀a b,Union (pair x y) (pair z w) a b→φ a b) : φ x y∧φ z w :=
  ⟨h x y (Or.inl ⟨rfl,rfl⟩),h z w (Or.inr ⟨rfl,rfl⟩)⟩
theorem star_55_42 (φ:α→α→Prop) (x y z w:α) :
    (∃a b,Union (pair x y) (pair z w) a b∧φ a b) ↔ φ x y∨φ z w := by
  constructor
  · rintro ⟨a,b,h,hab⟩; exact h.elim (fun e=>e.1.symm ▸ e.2.symm ▸ Or.inl hab) (fun e=>e.1.symm ▸ e.2.symm ▸ Or.inr hab)
  · rintro (h|h); exact ⟨x,y,Or.inl ⟨rfl,rfl⟩,h⟩; exact ⟨z,w,Or.inr ⟨rfl,rfl⟩,h⟩
theorem star_55_43 (x y z w c d:α) (h:Union (pair x y) (pair z w)=Union (pair x y) (pair c d))
    (hne:pair z w≠pair x y) : pair z w=pair c d := by
  have q:Union (pair x y) (pair c d) z w:=by rw[←h];exact Or.inr ⟨rfl,rfl⟩
  rcases q with q|q; exact (hne ((star_55_202 z w x y).mpr q)).elim; exact (star_55_202 z w c d).mpr q
theorem star_55_431 (x y z w a b c d:α)
    (h:Union (pair x y) (pair z w)=Union (pair a b) (pair c d)) : (x=a∧y=b)∨(x=c∧y=d) := by
  have q:Union (pair a b) (pair c d) x y:=by rw[←h];exact Or.inl ⟨rfl,rfl⟩
  exact q
theorem star_55_44 (x y z w a b c d:α)
    (h:Union (pair x y) (pair z w)=Union (pair a b) (pair c d)) (hne:pair x y≠pair z w) :
    ((x=a∧y=b)∧(z=c∧w=d))∨((x=c∧y=d)∧(z=a∧w=b)) := by
  have p:=star_55_431 x y z w a b c d h
  have hs : Union (pair z w) (pair x y)=Union (pair a b) (pair c d) := by
    rw [show Union (pair z w) (pair x y)=Union (pair x y) (pair z w) by apply rel_ext; intro u v; exact or_comm]
    exact h
  have q:=(star_55_431 z w x y a b c d hs)
  rcases p with p|p <;> rcases q with q|q
  · exact (hne ((star_55_202 x y z w).mpr ⟨p.1.trans q.1.symm,p.2.trans q.2.symm⟩)).elim
  · exact Or.inl ⟨p,q⟩
  · exact Or.inr ⟨p,q⟩
  · exact (hne ((star_55_202 x y z w).mpr ⟨p.1.trans q.1.symm,p.2.trans q.2.symm⟩)).elim
theorem star_55_5 (R:Rel α) (x y z w:α) (h:Included R (Union (pair x y) (pair z w))) :
    R=EmptyRel∨R=pair x y∨R=pair z w∨R=Union (pair x y) (pair z w) := by
  classical
  by_cases hx:R x y <;> by_cases hz:R z w
  · right;right;right;apply rel_ext;intro a b;constructor;exact h a b;intro q;exact q.elim (fun e=>e.1.symm▸e.2.symm▸hx) (fun e=>e.1.symm▸e.2.symm▸hz)
  · right;left;apply rel_ext;intro a b;constructor;intro q;exact (h a b q).resolve_right (fun e=>hz (e.1.symm▸e.2.symm▸q));rintro ⟨rfl,rfl⟩;exact hx
  · right;right;left;apply rel_ext;intro a b;constructor;intro q;exact (h a b q).resolve_left (fun e=>hx (e.1.symm▸e.2.symm▸q));rintro ⟨rfl,rfl⟩;exact hz
  · left; apply rel_ext; intro a b; constructor
    · intro q; rcases h a b q with e|e
      · exact (hx (e.1.symm ▸ e.2.symm ▸ q)).elim
      · exact (hz (e.1.symm ▸ e.2.symm ▸ q)).elim
    · exact False.elim
theorem star_55_52 (x y:α) : x=y ↔ Included (pair x y) Identity := by
  constructor
  · rintro rfl a b ⟨rfl,rfl⟩; rfl
  · intro h; exact h x y ⟨rfl,rfl⟩
theorem star_55_521 (x y:α) : x≠y ↔ Included (pair x y) Diversity := by
  constructor
  · intro hn a b ⟨rfl,rfl⟩; exact hn
  · intro h e; exact h x y ⟨rfl,rfl⟩ e
theorem star_55_53 (x y:α) (h:x≠y) :
    Included (pair x y) Diversity ∧ Included (pair y x) Diversity :=
  ⟨(by intro a b hab; rcases hab with ⟨rfl,rfl⟩; exact h),
   (by intro a b hab; rcases hab with ⟨rfl,rfl⟩; exact fun e=>h e.symm)⟩
end PM.Architecture.Star55FiniteKernel
