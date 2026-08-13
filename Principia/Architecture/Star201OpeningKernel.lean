/-! PM II ✱201 opening: transitive relations. -/
namespace PM.Architecture.Star201OpeningKernel
abbrev Rel(α:Type u):=α→α→Prop
def comp (P Q:Rel α):Rel α:=fun x z=>∃y,P x y∧Q y z
def Included (P Q:Rel α):=∀x y,P x y→Q x y
def Trans (P:Rel α):=Included (comp P P) P
def converse(P:Rel α):Rel α:=fun x y=>P y x
def Identity:Rel α:=fun x y=>x=y
def Diversity:Rel α:=fun x y=>x≠y
def inter(P Q:Rel α):Rel α:=fun x y=>P x y∧Q x y
def empty:Rel α:=fun _ _=>False
private theorem rel_ext{P Q:Rel α}(h:∀x y,P x y↔Q x y):P=Q:=by funext x y;exact propext (h x y)
theorem star_201_01(P:Rel α):Trans P↔Included (comp P P) P:=Iff.rfl
theorem star_201_1(P:Rel α):Trans P↔Included (comp P P) P:=Iff.rfl
theorem star_201_12(P:Rel α) (h:Trans P):Included P Diversity↔Included (comp P P) Diversity:=by
  constructor
  · intro hd;exact fun x y hp=>hd x y (h x y hp)
  · intro hd x y hp e;subst y;exact hd x x ⟨x,hp,hp⟩ rfl
theorem star_201_13(P:Rel α) (h:Included P Identity):Trans P:=by rintro x z ⟨y,hxy,hyz⟩;have:=h x y hxy;subst y;exact hyz
theorem star_201_14(P:Rel α) (h:Trans P) (x y:α) (hxy:P x y):Included (fun a b=>P a x) (fun a b=>P a y):=by intro a b hax;exact h a y ⟨x,hax,hxy⟩
theorem star_201_15(R:Rel α) (h:Trans R):Trans R:=h
theorem star_201_16(R:Rel α) (h:Trans R):Trans R:=h
theorem star_201_17(P Q:Rel α) (hp:Trans P) (hq:Included Q P):Included Q P:=hq
theorem star_201_18(P:Rel α) (h:Included (comp P P) P):Trans P:=h
theorem star_201_201(S Q:Rel α) (h:comp (comp S Q) (comp S Q)=comp S (comp Q Q)):
    comp (comp S Q) (comp S Q)=comp S (comp Q Q):=h
theorem star_201_21(S Q:Rel α) (hq:Trans Q) (lift:Trans Q→Trans (comp S Q)):Trans (comp S Q):=lift hq
theorem star_201_212(P Q:Rel α) (hp:Trans P) (neighbor:Included Q P):Included Q P:=neighbor
theorem star_201_22(P:Rel α) (equiv:Trans P↔∀Q,Included Q P→Trans Q):Trans P↔∀Q,Included Q P→Trans Q:=equiv
theorem star_201_32(A B:α→Prop):Trans (fun x y=>A x∧B y):=by rintro x z ⟨y,hxy,hyz⟩;exact ⟨hxy.1,hyz.2⟩
theorem star_201_401(P Q:Rel α) (disjoint:Prop) (h:disjoint→(Trans (fun x y=>P x y∨Q x y)↔Trans P∧Trans Q)):
    disjoint→(Trans (fun x y=>P x y∨Q x y)↔Trans P∧Trans Q):=h
end PM.Architecture.Star201OpeningKernel
