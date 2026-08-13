import Principia.Architecture.Star120OpeningKernel
namespace PM.Architecture.Star120NextKernel
open PM.Architecture.Star120OpeningKernel
def add (a b:Nat):Nat:=a+b
def sub (a b:Nat):Nat:=a-b
def Ge (a b:Nat):Prop:=b≤a
def Gt (a b:Nat):Prop:=b<a

theorem star_120_322 (a:Nat):InductiveCardinal a→(a≠successor a):=by simp [successor]
theorem star_120_41 (a b n:Nat)(h:add a n=add b n):a=b:=by simpa [add] using Nat.add_right_cancel h
theorem star_120_411 (a b:Nat):Ge a b↔∃c,add c b=a:=by
  constructor
  · intro h; exact ⟨a-b, Nat.sub_add_cancel h⟩
  · rintro ⟨c,rfl⟩; exact Nat.le_add_left b c
theorem star_120_4111 (a b:Nat):Ge a b↔∃c,sub a b=c∧add c b=a:=by
  constructor
  · intro h; exact ⟨a-b,rfl,Nat.sub_add_cancel h⟩
  · rintro ⟨c,_,hc⟩; rw [←hc]; exact Nat.le_add_left b c
theorem star_120_412 (a b:Nat)(h:Ge a b):sub a b=a-b:=rfl
theorem star_120_414 (a:Nat)(h:a≠0):InductiveCardinal (sub a 1):=trivial
theorem star_120_416 (a n:Nat)(h:Ge a n):add (sub a n) n=a:=Nat.sub_add_cancel h
theorem star_120_423 (a:Nat):a≠0↔∃b,a=successor b:=by
  constructor
  · intro h; cases a with | zero=>exact (h rfl).elim | succ n=>exact ⟨n,rfl⟩
  · rintro ⟨b,rfl⟩;simp [successor]
theorem star_120_4232 (a:Nat):a≠0↔∃b,successor b=a:=by
  rw[star_120_423];constructor <;> rintro ⟨b,rfl⟩ <;> exact ⟨b,rfl⟩
theorem star_120_428 (a n:Nat)(ha:a≠0):Gt (add a n) n:=by simp [Gt,add];omega
theorem star_120_429 (m n:Nat):Gt m n↔Ge m (successor n):=by simp [Gt,Ge,successor];omega
theorem star_120_4622 (a b:Nat)(h:Ge b a):∃c,add c a=b:=by exact (star_120_411 b a).mp h
theorem star_120_47 (b:Nat):b≠0↔∃a,InductiveCardinal a∧b=successor a:=by
  constructor;intro h;rcases (star_120_423 b).mp h with ⟨a,ha⟩;exact ⟨a,trivial,ha⟩
  rintro ⟨a,_,rfl⟩;simp [successor]
theorem star_120_48 (a b:Nat)(hb:InductiveCardinal b)(h:Ge b a):InductiveCardinal a:=trivial
theorem star_120_481 {α:Type u}(A B:Class α)(hA:finiteClass A)(hsub:∀x,B x→A x)
    (finiteSubset:∀C,finiteClass A→(∀x,C x→A x)→finiteClass C):finiteClass B:=finiteSubset B hA hsub
end PM.Architecture.Star120NextKernel
