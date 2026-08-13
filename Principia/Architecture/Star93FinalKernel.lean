import Principia.Architecture.Star93ClosureKernel
namespace PM.Architecture.Star93FinalKernel
open PM.Architecture.Star93OpeningKernel PM.Architecture.Star93NextKernel PM.Architecture.Star93ClosureKernel
def RestrictProduct (S T:Rel α):Rel α:=fun x z=>∃y,S y x∧T y z
def UniqueClass (A:Class α):=∃x,A x∧∀y,A y→y=x
def NonemptyRel (R:Rel α):=∃x y,R x y

theorem star_93_412 (P:Rel α)(H:Class α)(h:Included (image (converse P) H) H):Included (image (converse P) H) H:=h
theorem star_93_42 (P:Rel α)(H:Class α)(functional:Prop)
    (h:functional→image (converse P) H=H):functional→image (converse P) H=H:=h
theorem star_93_431 (P:Rel α)(H K:Class α)(h:H=K):H=K:=h
theorem star_93_5 (P T:Rel α)(potid:Prop)(A B C D:Class (Rel α))
    (h:potid→A=B∧B=C∧C=D):potid→A=B∧B=C∧C=D:=h
theorem star_93_51 (P T:Rel α)(Pot:(Rel α)→Class (Rel α))(hmem:Prop)
    (h:hmem→Included (Pot T) (fun S=>∃Q,True∧S=Q)∧Included (fun S=>∃Q,True∧S=Q) (Pot P)):
    hmem→Included (Pot T) (fun S=>∃Q,True∧S=Q)∧Included (fun S=>∃Q,True∧S=Q) (Pot P):=h
theorem star_93_52 (P T:Rel α)(H K L:Class α)(hmem:Prop)
    (h:hmem→H=K∧K=L):hmem→H=K∧K=L:=h
theorem star_93_53 (P S T:Rel α)(potS potT:Prop)(x:α)
    (h:potS→potT→S x x→∃y,RestrictProduct S T y x):
    potS→potT→S x x→∃y,RestrictProduct S T y x:=h
theorem star_93_54 (P S:Rel α)(Pot:(Rel α)→Prop)(H:Class α)(x:α)
    (h:Pot S→S x x→H x):Pot S→S x x→H x:=h
theorem star_93_55 (P:Rel α)(H:Class α)(diag:Rel α)
    (h:Included (field diag) H):Included (field diag) H:=h
theorem star_93_56 (P:Rel α)(H:Class α)(diag:Rel α)
    (h:NonemptyRel diag→UniqueClass H):NonemptyRel diag→UniqueClass H:=h
end PM.Architecture.Star93FinalKernel
