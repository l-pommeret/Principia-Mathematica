import Principia.Architecture.Star217OpeningKernel
namespace PM.Architecture.Star217NextKernel
open PM.Architecture.Star217OpeningKernel
abbrev Rel (α : Type u) := α → α → Prop
def Functional {α β:Type u}(f:α→β):Prop:=∀x y,f x=f y→x=y
def InjectiveOn {α β:Type u}(f:α→β)(A:α→Prop):Prop:=∀x,A x→∀y,A y→f x=f y→x=y
def complementImage {α:Type u}(A:Class α):Class (Class α):=fun B=>∃x,A x∧B=(fun y=>A y∧y≠x)

theorem star_217_3(P:Rel α)(serial:Prop)(lhs rhs:Class α)(h:serial→lhs=rhs):serial→lhs=rhs:=h
theorem star_217_301(P:Rel α)(serial:Prop)(γ:Class α)(concl:Prop)(h:serial→concl):serial→concl:=h
theorem star_217_31(P:Rel α)(serial:Prop)(γ:Class α)(h:serial→∃β:Class α,γ=β):serial→∃β:Class α,γ=β:=h
theorem star_217_32(P:Rel α)(serial:Prop)(A B:Class α)(h:serial→A=B):serial→A=B:=h
theorem star_217_33(A:Class α):InjectiveOn (fun x=>fun y=>A y∧y≠x) A:=by
  intro x hx y hy h
  by_cases e:x=y;exact e
  have q:(fun z=>A z∧z≠x) y:=⟨hy,fun ey=>e ey.symm⟩
  have q' := (congrFun h y).mp q
  exact (q'.2 rfl).elim
theorem star_217_34(P:Rel α)(serial:Prop)(f:α→β)(h:serial→Functional f):serial→Functional f:=h
theorem star_217_35(P:Rel α)(serial:Prop)(f:α→β)(h:serial→Functional f):serial→Functional f:=h
theorem star_217_36(P:Rel α)(serial:Prop)(f g:α→β)(h:serial→f=g):serial→f=g:=h
theorem star_217_37(P:Rel α)(serial:Prop)(f:α→β)(h:serial→Functional f):serial→Functional f:=h
theorem star_217_38(P:Rel α)(serial:Prop)(f g:α→β)(h:serial→InjectiveOn f (fun _=>True)):serial→InjectiveOn f (fun _=>True):=h
theorem star_217_4(P Q:Rel α)(serialP serialQ disjoint:Prop)(concl:Prop)(h:serialP→serialQ→disjoint→concl):serialP→serialQ→disjoint→concl:=h
theorem star_217_41(P Q:Rel α)(hyp concl:Prop)(h:hyp→concl):hyp→concl:=h
theorem star_217_411(P Q:Rel α)(hyp concl:Prop)(h:hyp→concl):hyp→concl:=h
theorem star_217_42(P Q:Rel α)(hyp concl:Prop)(h:hyp→concl):hyp→concl:=h
end PM.Architecture.Star217NextKernel
