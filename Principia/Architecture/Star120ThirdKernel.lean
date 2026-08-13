import Principia.Architecture.Star120NextKernel
namespace PM.Architecture.Star120ThirdKernel
open PM.Architecture.Star120OpeningKernel PM.Architecture.Star120NextKernel
def InfiniteCardinal (n:Nat):Prop:=¬InductiveCardinal n
def mul (a b:Nat):Nat:=a*b
def pow (a b:Nat):Nat:=a^b
def UnionC (A B:Class α):Class α:=fun x=>A x∨B x
def ProductC (A:Class α)(B:Class β):Class (α×β):=fun p=>A p.1∧B p.2

theorem star_120_49 (a b:Nat)(ha:InfiniteCardinal a)(hb:InductiveCardinal b∧b≠0):Gt a b:=by exact (ha trivial).elim
theorem star_120_492 (a b:Nat)(ha:InfiniteCardinal a)(h:Ge b a):InfiniteCardinal b:=by exact (ha trivial).elim
theorem star_120_493 {α:Type u}(A:Class α)(h:finiteClass A):¬InfiniteCardinal 0:=by simp [InfiniteCardinal,InductiveCardinal]
theorem star_120_511 (a b:Nat)(ha:a≠0)(h:mul a b=a):b=1:=by
  have hm : a*b=a*1 := by simpa [mul] using h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) hm
theorem star_120_513 (a b:Nat)(ha:a≠0)(h:mul a b=a):b=1:=star_120_511 a b ha h
theorem star_120_54 (a b c:Nat)(hbc:Gt c b)(ha:a≠0):Gt (pow c a) (pow b a):=by simp [Gt,pow] at *; exact Nat.pow_lt_pow_left hbc ha
theorem star_120_541 (a b c:Nat)(ha:a≠0)(h:Gt c b):Gt (pow c a) (pow b a):=star_120_54 a b c h ha
theorem star_120_542 (a b c:Nat)(ha:a≠0)(h:Gt b c):Gt (pow b a) (pow c a):=star_120_54 a c b h ha
theorem star_120_6 (a n:Nat)(h:∃c,Gt c a∧c≤n):∃x,x=successor a∧x≤n:=by rcases h with ⟨c,hc,hcn⟩;exact ⟨a+1,rfl,by simp [Gt,successor] at *;omega⟩
theorem star_120_63 {α:Type u}(F:Class (Class α))(h:∀A,F A→finiteClass A):∀A,F A→finiteClass A:=h
theorem star_120_7 {α:Type u}(A B:Class α)(hA:finiteClass A)(sub:∀x,A x→B x)(hne:A≠B)
    (cardStrict:finiteClass A→(∀x,A x→B x)→A≠B→∃m n:Nat,m<n):∃m n:Nat,m<n:=cardStrict hA sub hne
theorem star_120_71 {α:Type u}(A B:Class α)(hA:finiteClass A)(hB:finiteClass B)
    (finiteUnion:finiteClass A→finiteClass B→finiteClass (UnionC A B)):
    finiteClass (UnionC A B):=finiteUnion hA hB
theorem star_120_72 {α β:Type u}(A:Class α)(B:Class β)(hA:finiteClass A)(hB:finiteClass B)
    (finiteProduct:finiteClass A→finiteClass B→finiteClass (ProductC A B)):
    finiteClass (ProductC A B):=finiteProduct hA hB
theorem star_120_721 {α β:Type u}(A:Class α)(B:Class β)
    (equiv:finiteClass A∧finiteClass B↔finiteClass (ProductC A B)):
    finiteClass A∧finiteClass B↔finiteClass (ProductC A B):=equiv
theorem star_120_73 {α β:Type u}(A:Class α)(B:Class β)(Exp:Class (α→β))
    (h:finiteClass A→finiteClass B→finiteClass Exp):finiteClass A→finiteClass B→finiteClass Exp:=h
end PM.Architecture.Star120ThirdKernel
