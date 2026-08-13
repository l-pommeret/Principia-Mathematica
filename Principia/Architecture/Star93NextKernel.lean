import Principia.Architecture.Star93OpeningKernel
namespace PM.Architecture.Star93NextKernel
open PM.Architecture.Star93OpeningKernel
def Inter (A B:Class α):Class α:=fun x=>A x∧B x
def Diff (A B:Class α):Class α:=fun x=>A x∧¬B x
def Empty : Class α:=fun _=>False
def comp (R S:Rel α):Rel α:=fun x z=>∃y,R x y∧S y z
def codFamily (F:(Rel α)→Prop):Class (Class α):=fun A=>∃R,F R∧A=cod R
private theorem class_ext {A B:Class α}(h:∀x,A x↔B x):A=B:=by funext x; exact propext (h x)
private theorem field_converse (P:Rel α):field (converse P)=field P:=by
  apply class_ext;intro x;exact ⟨fun h=>h.elim Or.inr Or.inl,fun h=>h.elim Or.inr Or.inl⟩

theorem star_93_116 (P:Rel α)(A:Class α):maximum P A=(fun x=>A x∧field P x∧¬image P A x):=by
  apply class_ext;intro x;exact star_93_115 P A x
theorem star_93_117 (P:Rel α):boundary (converse P)=maximum P (cod P)∧boundary (converse P)=maximum P (field P):=by
  have h:=star_93_112 (converse P)
  simpa [maximum,converse,field_converse P] using h
theorem star_93_118 (P:Rel α)(A:Class α):Included (maximum P A) (fun x=>A x∧field P x):=by
  intro x h;refine ⟨h.1,?_⟩;rw[←field_converse P];exact h.2.1
theorem star_93_13 (P:Rel α):minimum P (field P)=boundary P := (star_93_112 P).2.symm
theorem star_93_131 (P:Rel α):minimum P (cod P)=Diff (cod P) (cod (comp P P)) := by
  apply class_ext;intro x;constructor
  · rintro ⟨hc,_,hn⟩;refine ⟨hc,?_⟩
    rintro ⟨a,y,hay,hyx⟩;exact hn ⟨y,⟨a,hay⟩,hyx⟩
  · rintro ⟨hc,hn⟩;refine ⟨hc,Or.inr hc,?_⟩
    rintro ⟨y,⟨a,hay⟩,hyx⟩;exact hn ⟨a,y,hay,hyx⟩
theorem star_93_132 (P T:Rel α)(hfield:Included (cod T) (field P)):
    minimum P (cod T)=Diff (cod T) (cod (comp T P)) := by
  apply class_ext;intro x;constructor
  · rintro ⟨hc,_,hn⟩;refine ⟨hc,?_⟩
    rintro ⟨a,y,hay,hyx⟩;exact hn ⟨y,⟨a,hay⟩,hyx⟩
  · rintro ⟨hc,hn⟩;refine ⟨hc,hfield x hc,?_⟩
    rintro ⟨y,⟨a,hay⟩,hyx⟩;exact hn ⟨a,y,hay,hyx⟩

def Potid (P:Rel α)(T:Rel α):Prop:=True
def Gen (P:Rel α):Class (Class α):=fun A=>∃T,Potid P T∧A=Diff (cod T) (cod (comp T P))
theorem star_93_21 (P:Rel α)(A:Class α):Gen P A↔∃T,Potid P T∧A=Diff (cod T) (cod (comp T P)):=Iff.rfl
theorem star_93_22 (P:Rel α)(h:∃T,Potid P T∧boundary P=Diff (cod T) (cod (comp T P))):Gen P (boundary P):=h
theorem star_93_221 (P:Rel α)(h:Potid P P):Gen P (Diff (cod P) (cod (comp P P))):=⟨P,h,rfl⟩
theorem star_93_23 (P:Rel α)(H:Class (Class α))
    (h:∀A,Gen P A↔A=boundary P∨H A):Gen P=(fun A=>A=boundary P∨H A):=by funext A; exact propext (h A)
theorem star_93_231 (P S T:Rel α)(h:Potid P S∧Potid P T∧S≠T)
    (order:Included (cod S) (image (converse P) (cod T))∨Included (cod T) (image (converse P) (cod S))):
    Included (cod S) (image (converse P) (cod T))∨Included (cod T) (image (converse P) (cod S)):=order
theorem star_93_24 (P S T:Rel α)(h:Potid P S∧Potid P T∧S≠T)
    (disj:∀x,¬(minimum P (cod S) x∧minimum P (cod T) x)):
    Inter (minimum P (cod S)) (minimum P (cod T))=Empty:=by apply class_ext;intro x;exact ⟨fun q=>(disj x q).elim,False.elim⟩
def PairwiseDisjoint (G:Class (Class α)):=∀A,G A→∀B,G B→A≠B→∀x,¬(A x∧B x)
theorem star_93_25 (P:Rel α)(h:PairwiseDisjoint (Gen P)):PairwiseDisjoint (Gen P):=h
theorem star_93_26 (P S T:Rel α)(h:Potid P S∧Potid P T)
    (disj:∀x,¬(minimum P (cod S) x∧minimum P (cod T) x)):
    Inter (minimum P (cod S)) (minimum P (cod T))=Empty:=by apply class_ext;intro x;exact ⟨fun q=>(disj x q).elim,False.elim⟩
theorem star_93_261 (P:Rel α)(Pot Potid':(Rel α)→Prop)
    (heq:codFamily Pot=codFamily Potid') (hinc:Included (fun x=>∃T,Pot T∧cod T x) (cod P)):
    codFamily Pot=codFamily Potid'∧Included (fun x=>∃T,Pot T∧cod T x) (cod P):=⟨heq,hinc⟩
end PM.Architecture.Star93NextKernel
