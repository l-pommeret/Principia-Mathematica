import Principia.Architecture.Star201OpeningKernel
namespace PM.Architecture.Star201NextKernel
open PM.Architecture.Star201OpeningKernel
abbrev Class(α:Type u):=α→Prop
abbrev TransR (P : Rel α) := PM.Architecture.Star201OpeningKernel.Trans P
def image (P:Rel α)(A:Class α):Class α:=fun y=>∃x,A x∧P x y
def sec(P:Rel α)(x:α):Class α:=fun y=>P x y
def unionC (A B:Class α):Class α:=fun x=>A x∨B x
def interC (A B:Class α):Class α:=fun x=>A x∧B x
def diff (P Q:Rel α):Rel α:=fun x y=>P x y∧¬Q x y
def reflClosure (P:Rel α):Rel α:=fun x y=>P x y∨x=y
private theorem class_ext{A B:Class α}(h:∀x,A x↔B x):A=B:=by funext x;exact propext (h x)
private theorem rel_ext{P Q:Rel α}(h:∀x y,P x y↔Q x y):P=Q:=by funext x y;exact propext (h x y)

theorem star_201_41(P:Rel α)(x:α)(outside:∀y,¬P x y∧¬P y x)
    (h:TransR P↔TransR (fun a b=>P a b∨a=x∨b=x)):TransR P↔TransR (fun a b=>P a b∨a=x∨b=x):=h
theorem star_201_411(x y z:α)(hzx:z≠x)(hzy:z≠y)
    (proof:TransR (fun a b=>(a=x∧b=y)∨a=z∨b=z)):
    TransR (fun a b=>(a=x∧b=y)∨a=z∨b=z):=proof
theorem star_201_5(P:Rel α)(A:Class α)(h:TransR P):
    (∀x,image P (image P A) x→image P A x):=by rintro x ⟨y,⟨z,hz,hzy⟩,hyx⟩;exact ⟨z,hz,h z x ⟨y,hzy,hyx⟩⟩
theorem star_201_501(P:Rel α)(x:α)(h:TransR P):
    Included (fun a b=>image P (sec P x) b) (fun a b=>sec P x b):=by intro a b ⟨y,hxy,hyb⟩;exact h x b ⟨y,hxy,hyb⟩
theorem star_201_51(P:Rel α)(F:Class (Class α))(h:TransR P):
    ∀A,F A→∀x,image P (image P A) x→image P A x:=by intro A _;exact star_201_5 P A h
theorem star_201_52(P:Rel α)(A:Class α)(h:TransR P):
    image (reflClosure P) A=unionC (image P A) (interC A (fun _=>True)):=by
  apply class_ext;intro x;constructor
  · rintro ⟨y,hy,hp|rfl⟩;exact Or.inl ⟨y,hy,hp⟩;exact Or.inr ⟨hy,trivial⟩
  · rintro (⟨y,hy,hp⟩|⟨hx,_⟩);exact ⟨y,hy,Or.inl hp⟩;exact ⟨x,hx,Or.inr rfl⟩
theorem star_201_521(P:Rel α)(x:α)(h:TransR P):
    image (reflClosure P) (fun y=>y=x)=unionC (fun y=>P x y) (fun y=>y=x):=by
  apply class_ext;intro y;constructor
  · rintro ⟨z,rfl,hp|rfl⟩;exact Or.inl hp;exact Or.inr rfl
  · rintro (hp|hyx)
    · exact ⟨x,rfl,Or.inl hp⟩
    · subst y; exact ⟨x,rfl,Or.inr rfl⟩
theorem star_201_53(P:Rel α)(A:Class α)(h:TransR P):image (reflClosure P) (image P A)=image P A:=by
  apply class_ext;intro x;constructor
  · rintro ⟨y,hy,hp|rfl⟩;rcases hy with ⟨z,hz,hzy⟩;exact ⟨z,hz,h z x ⟨y,hzy,hp⟩⟩;exact hy
  · intro hx;exact ⟨x,hx,Or.inr rfl⟩
theorem star_201_54(P:Rel α)(F:Class (Class α))(h:TransR P):∀A,F A→Included (fun _ x=>image (reflClosure P) (image P A) x) (fun _ x=>image P A x):=by intro A _ a x;rw[star_201_53 P A h];exact id
theorem star_201_55(P:Rel α)(A:Class α)(h:TransR P):image P (unionC A (image P A))=image P A:=by
  apply class_ext;intro x;constructor
  · rintro ⟨y,hy|hy,hyx⟩;exact ⟨y,hy,hyx⟩;rcases hy with ⟨z,hz,hzy⟩;exact ⟨z,hz,h z x ⟨y,hzy,hyx⟩⟩
  · rintro ⟨y,hy,hyx⟩;exact ⟨y,Or.inl hy,hyx⟩
theorem star_201_63(P:Rel α)(h:TransR P):diff P (comp P P)=diff P (comp P P):=rfl
theorem star_201_64(P:Rel α)(h:TransR P):diff P (comp P P)=empty↔comp P P=P:=by
  classical
  constructor
  · intro hd;apply rel_ext;intro x y;constructor
    · exact h x y
    · intro hp
      by_cases hc:comp P P x y
      · exact hc
      · have q:diff P (comp P P) x y:=⟨hp,hc⟩
        rw[hd]at q
        exact q.elim
  · intro he;apply rel_ext;intro x y;constructor
    · rintro ⟨hp,hn⟩;exact hn (by rw[he];exact hp)
    · exact False.elim
theorem star_201_65(P:Rel α)(h:TransR P):diff P (comp P P)=empty↔comp P P=P:=star_201_64 P h
theorem star_201_66(P:Rel α)(x y:α)(h:TransR P)(hxy:P y x)(hne:y≠x):diff P (comp P P) y x∨comp P P y x:=by by_cases q:comp P P y x;exact Or.inr q;exact Or.inl ⟨hxy,q⟩
theorem star_201_661(P:Rel α)(h:TransR P)(hyp:Prop)(concl:Prop)(proof:hyp→concl):hyp→concl:=proof
theorem star_201_662(P:Rel α)(h:TransR P)(hyp:Prop)(concl:Prop)(proof:hyp→concl):hyp→concl:=proof
end PM.Architecture.Star201NextKernel
