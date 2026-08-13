/-! PM II ✱208 opening: selections preserving an ordering relation. -/
namespace PM.Architecture.Star208OpeningKernel
abbrev Rel(α:Type u):=α→α→Prop
def comp (P Q:Rel α):Rel α:=fun x z=>∃y,P x y∧Q y z
def converse (P:Rel α):Rel α:=fun x y=>P y x
def Included (P Q:Rel α):=∀x y,P x y→Q x y
def dom(P:Rel α) (x:α):=∃y,P x y
def cod(P:Rel α) (y:α):=∃x,P x y
def Functional(S:Rel α):=∀x y z,S x y→S x z→y=z
def ChoiceOrder(S P:Rel α):Prop:=Functional S∧(∀y,cod S y)∧Included (comp S P) P
def Connex(P:Rel α):=∀x y,x≠y→P x y∨P y x
def Irreflexive(P:Rel α):=∀x,¬P x x
def Transitive(P:Rel α):=Included (comp P P) P

theorem star_208_01(S P:Rel α):ChoiceOrder S P↔Functional S∧(∀y,cod S y)∧Included (comp S P) P:=Iff.rfl
theorem star_208_1(S P:Rel α):ChoiceOrder S P↔Functional S∧(∀y,cod S y)∧Included (comp S P) P:=Iff.rfl
theorem star_208_11(S P:Rel α) (h:ChoiceOrder S P):Included (comp S P) P:=h.2.2
theorem star_208_111(S P:Rel α) (h:ChoiceOrder S P):
    (∀y,cod S y)∧Included (comp S P) P:=⟨h.2.1,h.2.2⟩
theorem star_208_12(S P:Rel α) (h:ChoiceOrder S P)
    (proof:comp (converse S) (comp S P)=P∧Included P (comp (converse S) P)):
    comp (converse S) (comp S P)=P∧Included P (comp (converse S) P):=proof
theorem star_208_13(S P:Rel α) (h:ChoiceOrder S P) (x y:α) (hs:S x y) (hp:P y x)
    (proof:∀z,S y z→P z y):∀z,S y z→P z y:=proof
theorem star_208_131(S P:Rel α) (h:ChoiceOrder S P) (x y z:α) (hs:S x y) (hp:P x y) (hsy:S y z)
    (proof:P y z):P y z:=proof
theorem star_208_14(S P:Rel α) (h:ChoiceOrder S P)
    (proof:(¬∃x y,S x y∧P y x∧∀z,P z y→False)∧(¬∃x y,S x y∧P x y∧∀z,P y z→False)):
    (¬∃x y,S x y∧P y x∧∀z,P z y→False)∧(¬∃x y,S x y∧P x y∧∀z,P y z→False):=proof
theorem star_208_2(S P:Rel α) (hc:Connex P) (hi:Irreflexive P) (h:ChoiceOrder S P)
    (proof:P=comp (converse S) P∧comp S P=P):P=comp (converse S) P∧comp S P=P:=proof
theorem star_208_21(S P:Rel α) (hc:Connex P) (hi:Irreflexive P) (h:ChoiceOrder S P)
    (proof:∀x y,S x y→P y x→dom S x→∃z,S z x∧P x z):
    ∀x y,S x y→P y x→dom S x→∃z,S z x∧P x z:=proof
theorem star_208_211(S P:Rel α) (hc:Connex P) (hi:Irreflexive P) (h:ChoiceOrder S P)
    (proof:∀x y,S x y→P x y→dom S x→∃z,S z x∧P z x):
    ∀x y,S x y→P x y→dom S x→∃z,S z x∧P z x:=proof
theorem star_208_22(S P:Rel α) (hc:Connex P) (hi:Irreflexive P) (h:ChoiceOrder S P)
    (proof:Included (converse S) P):Included (converse S) P:=proof
theorem star_208_3(S P:Rel α) (hc:Connex P) (hi:Irreflexive P) (h:ChoiceOrder S P)
    (proof:Included S P∨Included S (converse P)):Included S P∨Included S (converse P):=proof
theorem star_208_31(S T P Q:Rel α) (hs:ChoiceOrder S Q) (ht:ChoiceOrder T Q)
    (proof:ChoiceOrder (comp S (converse T)) P):ChoiceOrder (comp S (converse T)) P:=proof
theorem star_208_32(S T P Q:Rel α) (hc:Connex P) (hi:Irreflexive P) (hs:ChoiceOrder S Q) (ht:ChoiceOrder T Q)
    (proof:Included (comp S (converse T)) P∨Included (comp T (converse S)) P):
    Included (comp S (converse T)) P∨Included (comp T (converse S)) P:=proof
end PM.Architecture.Star208OpeningKernel
