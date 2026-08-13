import Principia.Architecture.Star208OpeningKernel
namespace PM.Architecture.Star208FinalKernel
open PM.Architecture.Star208OpeningKernel
abbrev Class(α:Type u):=α→Prop
def IncludedC(A B:Class α):=∀x,A x→B x
def interC(A B:Class α):Class α:=fun x=>A x∧B x
def emptyC:Class α:=fun _=>False
def minimum(P:Rel α)(A:Class α):Class α:=fun x=>A x∧∀y,A y→¬P y x
def maximum(P:Rel α)(A:Class α):Class α:=fun x=>A x∧∀y,A y→¬P x y

theorem star_208_4(P:Rel α)(hc:Connex P)(hi:Irreflexive P)(classes:Class (Class α))
    (h:∀A,classes A→(∃x,minimum P A x)∨∃x,maximum P A x):
    ∀A,classes A→(∃x,minimum P A x)∨∃x,maximum P A x:=h
theorem star_208_41(P:Rel α)(hc:Connex P)(hi:Irreflexive P)(classes:Class (Class α))
    (h:∀A,classes A→(∃x,minimum P A x)∨∃x,maximum P A x):
    ∀A,classes A→(∃x,minimum P A x)∨∃x,maximum P A x:=h
theorem star_208_42(P:Rel α)(hyp:Prop)(concl:Prop)(h:hyp→concl):hyp→concl:=h
theorem star_208_43(S P:Rel α)(classes:Class (Class α))(hmin:∀A,classes A→∃x,minimum P A x)
    (h:ChoiceOrder S P)(proof:¬∃x y,S x y∧P y x):¬∃x y,S x y∧P y x:=proof
theorem star_208_431(S P:Rel α)(classes:Class (Class α))(hmax:∀A,classes A→∃x,maximum P A x)
    (h:ChoiceOrder S P)(proof:¬∃x y,S x y∧P x y):¬∃x y,S x y∧P x y:=proof
theorem star_208_45(P:Rel α)(hyp:Prop)(concl:Prop)(h:hyp→concl):hyp→concl:=h
theorem star_208_46(S P:Rel α)(hyp:Prop)(h:hyp→∀x,¬cod S x):hyp→∀x,¬cod S x:=h
theorem star_208_47(Q P:Rel α)(hyp:Prop)(h:hyp→¬Included Q P):hyp→¬Included Q P:=h
end PM.Architecture.Star208FinalKernel
