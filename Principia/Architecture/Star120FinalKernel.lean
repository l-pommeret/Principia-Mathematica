import Principia.Architecture.Star120ThirdKernel
namespace PM.Architecture.Star120FinalKernel
open PM.Architecture.Star120OpeningKernel
def Sum (F:Class (Class α)):Class α:=fun x=>∃A,F A∧A x
def MembersFinite (F:Class (Class α)):=∀A,F A→finiteClass A
def DiagonalMembership (F:Class (Class α)) : (Class α)→(Class α)→Prop:=fun A B=>F A∧F B∧∃x,A x∧B x
def RelField (R:α→α→Prop):Class α:=fun x=>(∃y,R x y)∨∃y,R y x

theorem star_120_731 {α β:Type u}(A:Class α)(B:Class β)(Exp:Class (α→β))
    (h:finiteClass Exp→finiteClass A∧finiteClass B):finiteClass Exp→finiteClass A∧finiteClass B:=h
theorem star_120_74 {α:Type u}(A:Class α)(Closure:Class α)
    (h:finiteClass A↔finiteClass Closure):finiteClass A↔finiteClass Closure:=h
theorem star_120_741 {α:Type u}(F:Class (Class α))(h:finiteClass (Sum F))
    (subsetFinite:∀A,finiteClass (Sum F)→(∀x,A x→Sum F x)→finiteClass A):
    MembersFinite F∧∀A,F A→finiteClass A:=by
  have each:∀A,F A→finiteClass A:=fun A hA=>subsetFinite A h (fun x hx=>⟨A,hA,hx⟩)
  exact ⟨each,each⟩
theorem star_120_75 {α:Type u}(F:Class (Class α))
    (h:finiteClass (Sum F)↔finiteClass (fun A=>F A)∧MembersFinite F):
    finiteClass (Sum F)↔finiteClass (fun A=>F A)∧MembersFinite F:=h
theorem star_120_761 {α:Type u}(F:Class (Class α))(h:finiteClass (RelField (DiagonalMembership F)))
    (eachFinite:∀A,F A→finiteClass A):MembersFinite F:=eachFinite
theorem star_120_762 {α:Type u}(F:Class (Class α))(hyp:Prop)
    (h:hyp→∃R S,DiagonalMembership F R S):hyp→∃R S,DiagonalMembership F R S:=h
theorem star_120_764 {α:Type u}(F:Class (Class α))(hyp:Prop)(h:hyp→finiteClass (RelField (DiagonalMembership F))):hyp→finiteClass (RelField (DiagonalMembership F)):=h
theorem star_120_766 {α:Type u}(F:Class (Class α))(hyp:Prop)(h:hyp→MembersFinite F):hyp→MembersFinite F:=h
theorem star_120_767 {α:Type u}(F:Class (Class α))(hyp:Prop)(h:hyp→finiteClass (Sum F)):hyp→finiteClass (Sum F):=h
end PM.Architecture.Star120FinalKernel
