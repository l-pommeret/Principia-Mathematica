import Principia.Architecture.Star55FiniteKernel
namespace PM.Architecture.Star55FinalKernel
open PM.Architecture.Star55OpeningKernel PM.Architecture.Star55MiddleKernel PM.Architecture.Star55FiniteKernel

def comp (R S : Rel α) : Rel α := fun x z=>∃y,R x y∧S y z
def biComp (R : Rel α) (x y : α) (S : Rel α) : Rel α := comp (comp R (pair x y)) S
def Product (P Q : Rel α) : (α×α)→(α×α)→Prop := fun a b=>P a.1 b.1∧Q a.2 b.2
def NonemptyRel (R : Rel α) := ∃x y,R x y
private theorem rel_ext {R S : Rel α}(h:∀x y,R x y↔S x y):R=S:=by funext x y;exact propext (h x y)

theorem star_55_54 (R:Rel α)(x y:α)(hxy:x≠y)
    (hf:field R=(fun z=>z=x∨z=y)) (ha:PM.Architecture.Star55MiddleKernel.Inter R (converse R)=EmptyRel) :
    R=pair x y∨R=pair y x := by
  classical
  have hasym : ∀ {a b}, R a b → R b a → False := by
    intro a b hab hba
    have q : PM.Architecture.Star55MiddleKernel.Inter R (converse R) a b := ⟨hab,hba⟩
    rw [ha] at q
    exact q
  have hx : domain R x ∨ codomain R x := by
    have : field R x := by rw [hf]; exact Or.inl rfl
    exact this
  rcases hx with ⟨a,hxa⟩|⟨a,hax⟩
  · have fa : a=x∨a=y := by have q:field R a:=Or.inr ⟨x,hxa⟩; rwa [hf] at q
    rcases fa with haeq|haeq
    · subst a; exact (hasym hxa hxa).elim
    · subst a; left; apply rel_ext; intro u v; constructor
      · intro huv
        have fu:u=x∨u=y:=by have q:field R u:=Or.inl ⟨v,huv⟩;rwa[hf]at q
        have fv:v=x∨v=y:=by have q:field R v:=Or.inr ⟨u,huv⟩;rwa[hf]at q
        rcases fu with rfl|rfl <;> rcases fv with rfl|rfl
        · exact (hasym huv huv).elim
        · exact ⟨rfl,rfl⟩
        · exact (hasym huv hxa).elim
        · exact (hasym huv huv).elim
      · rintro ⟨rfl,rfl⟩; exact hxa
  · have fa : a=x∨a=y := by have q:field R a:=Or.inl ⟨x,hax⟩;rwa[hf]at q
    rcases fa with haeq|haeq
    · subst a; exact (hasym hax hax).elim
    · subst a; right; apply rel_ext; intro u v; constructor
      · intro huv
        have fu:u=x∨u=y:=by have q:field R u:=Or.inl ⟨v,huv⟩;rwa[hf]at q
        have fv:v=x∨v=y:=by have q:field R v:=Or.inr ⟨u,huv⟩;rwa[hf]at q
        rcases fu with rfl|rfl <;> rcases fv with rfl|rfl
        · exact (hasym huv huv).elim
        · exact (hasym huv hax).elim
        · exact ⟨rfl,rfl⟩
        · exact (hasym huv huv).elim
      · rintro ⟨rfl,rfl⟩; exact hax

theorem star_55_57 (R:Rel α)(x y:α) : comp R (pair x y)=cross (fun a=>R a x) (singleton y) := by
  apply rel_ext;intro a b;constructor
  · rintro ⟨z,haz,hz⟩;exact ⟨hz.1.symm▸haz,hz.2⟩
  · rintro ⟨hax,hby⟩;exact ⟨x,hax,rfl,hby⟩
theorem star_55_571 (x y:α)(S:Rel α) : comp (pair x y) S=cross (singleton x) (fun b=>S y b) := by
  apply rel_ext;intro a b;constructor
  · rintro ⟨z,haz,hzb⟩;exact ⟨haz.1,haz.2.symm▸hzb⟩
  · rintro ⟨hax,hyb⟩;exact ⟨y,⟨hax,rfl⟩,hyb⟩
theorem star_55_572 (R:Rel α)(x y:α)(S:Rel α) : biComp R x y S=cross (fun a=>R a x) (fun b=>S y b) := by
  apply rel_ext;intro a b;constructor
  · rintro ⟨z,⟨u,hau,hp⟩,hzb⟩;exact ⟨hp.1.symm▸hau,hp.2.symm▸hzb⟩
  · rintro ⟨hax,hyb⟩;exact ⟨y,⟨x,hax,⟨rfl,rfl⟩⟩,hyb⟩
theorem star_55_573 (R:Rel α)(x y:α)(S:Rel α) : biComp R x y (converse S)=cross (fun a=>R a x) (fun b=>S b y) := by
  simpa [converse] using star_55_572 R x y (converse S)
theorem star_55_58 (R:Rel α)(x y a:α)(h:∀z,R z x↔z=a) : comp R (pair x y)=pair a y := by
  rw[star_55_57];apply rel_ext;intro z w;change (R z x ∧ w=y) ↔ (z=a ∧ w=y);exact and_congr (h z) Iff.rfl
theorem star_55_581 (S:Rel α)(x y b:α)(h:∀z,S y z↔z=b) : comp (pair x y) S=pair x b := by
  rw[star_55_571];apply rel_ext;intro z w;change (z=x ∧ S y w) ↔ (z=x ∧ w=b);exact and_congr Iff.rfl (h w)
theorem star_55_582 (R S:Rel α)(x y a b:α)(hr:∀z,R z x↔z=a)(hs:∀z,S y z↔z=b) : biComp R x y S=pair a b := by
  rw[star_55_572];apply rel_ext;intro z w;change (R z x∧S y w)↔(z=a∧w=b);exact and_congr (hr z) (hs w)
theorem star_55_583 (R S:Rel α)(x y a b:α)(hr:∀z,R z x↔z=a)(hs:∀z,S z y↔z=b) : biComp R x y (converse S)=pair a b := by
  rw[star_55_573];apply rel_ext;intro z w;change (R z x∧S w y)↔(z=a∧w=b);exact and_congr (hr z) (hs w)
theorem star_55_6 (R S:Rel α)(z w:α) : Product R (converse S) (z,w) = fun q=>R z q.1∧S q.2 w := rfl
theorem star_55_61 (R S:Rel α)(z w a b:α)(hr:∀q,R z q↔q=a)(hs:∀q,S q w↔q=b) :
    Product R (converse S) (z,w) = fun q=>q=(a,b) := by funext q;apply propext;simpa [Product,converse,Prod.ext_iff,hr,hs]
theorem star_55_62 (x y z w:α)(h:z≠w) : (Union (pair x z) (pair y w)) x z ∧ (Union (pair x z) (pair y w)) y w := ⟨Or.inl ⟨rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
theorem star_55_621 (x y z w:α)(h:x≠y) : converse (Union (pair x z) (pair y w)) z x ∧ converse (Union (pair x z) (pair y w)) w y := ⟨Or.inl ⟨rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩

theorem star_55_63 (P Q R S:Rel α)(hn:NonemptyRel (PM.Architecture.Star55MiddleKernel.Inter Q S))(h:Product P Q=Product R S) : P=R := by
  rcases hn with ⟨q,s,hq,hs⟩;apply rel_ext;intro x y;constructor
  · intro hp;have e:=congrFun (congrFun h (x,q)) (y,s);exact (e.mp ⟨hp,hq⟩).1
  · intro hr;have e:=congrFun (congrFun h (x,q)) (y,s);exact (e.mpr ⟨hr,hs⟩).1
theorem star_55_631 (P Q R S:Rel α)(hn:NonemptyRel (PM.Architecture.Star55MiddleKernel.Inter P R))(h:Product P Q=Product R S) : Q=S := by
  rcases hn with ⟨p,r,hp,hr⟩;apply rel_ext;intro x y;constructor
  · intro hq;have e:=congrFun (congrFun h (p,x)) (r,y);exact (e.mp ⟨hp,hq⟩).2
  · intro hs;have e:=congrFun (congrFun h (p,x)) (r,y);exact (e.mpr ⟨hr,hs⟩).2
theorem star_55_632 (P Q R S:Rel α)(h:Product P Q=Product R S)(hp:NonemptyRel P)(hq:NonemptyRel Q) :
    NonemptyRel (PM.Architecture.Star55MiddleKernel.Inter P R)∧NonemptyRel (PM.Architecture.Star55MiddleKernel.Inter Q S) := by
  rcases hp with ⟨x,y,hp⟩;rcases hq with ⟨z,w,hq⟩
  have e:=congrFun (congrFun h (x,z)) (y,w);have rs:=e.mp ⟨hp,hq⟩
  exact ⟨⟨x,y,hp,rs.1⟩,z,w,hq,rs.2⟩
theorem star_55_64 (P Q R S:Rel α)(h:Product P Q=Product R S)(hp:NonemptyRel P)(hq:NonemptyRel Q) : P=R∧Q=S := by
  have hn:=star_55_632 P Q R S h hp hq
  exact ⟨star_55_63 P Q R S hn.2 h,star_55_631 P Q R S hn.1 h⟩
end PM.Architecture.Star55FinalKernel
