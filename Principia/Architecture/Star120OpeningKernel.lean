/-! PM II ✱120 opening: the inductive finite cardinals, represented by `Nat`. -/
namespace PM.Architecture.Star120OpeningKernel
abbrev Class (α:Type u):=α→Prop
def InductiveCardinal (n:Nat):Prop:=True
def successor (n:Nat):Nat:=n+1
def predecessor (n:Nat):Nat:=n-1
def finiteClass (A:Class α):Prop:=∃n:Nat,∃f:Fin n→α,∀x,A x↔∃i,f i=x
def Empty:Class α:=fun _=>False
def Singleton (x:α):Class α:=fun y=>y=x
def Insert (A:Class α)(x:α):Class α:=fun y=>A y∨y=x

theorem star_120_11 (φ:Nat→Prop)(n:Nat)(h0:φ 0)(hs:∀k,φ k→φ (successor k)):φ n:=by
  induction n with | zero=>exact h0 | succ n ih=>exact hs n ih
theorem star_120_12 : InductiveCardinal 0:=trivial
theorem star_120_121 (n:Nat)(h:InductiveCardinal n):InductiveCardinal (successor n):=trivial
theorem star_120_13 (φ:Nat→Prop)(n:Nat)(h0:φ 0)(hs:∀k,InductiveCardinal k→φ k→φ (successor k)):φ n:=by
  induction n with | zero=>exact h0 | succ n ih=>exact hs n trivial ih
theorem star_120_15 (n:Nat)(h:InductiveCardinal n):InductiveCardinal (successor n):=trivial
theorem star_120_151 (n:Nat)(h:InductiveCardinal n):InductiveCardinal (n+1):=trivial
theorem star_120_152 (n:Nat)(h:InductiveCardinal (successor n)∧successor n≠0):InductiveCardinal n∧n≠0∨n=0:=by
  rcases Nat.eq_zero_or_pos n with rfl|hn;exact Or.inr rfl;exact Or.inl ⟨trivial,Nat.ne_of_gt hn⟩
theorem star_120_21 (A:Class α):finiteClass A↔∃n:Nat,∃f:Fin n→α,∀x,A x↔∃i,f i=x:=Iff.rfl
theorem star_120_211 (A:Class α)(h:finiteClass A∧A≠Empty):finiteClass A:=h.1
theorem star_120_212 : finiteClass (Empty:Class α):=by exact ⟨0,Fin.elim0,fun x=>⟨False.elim,fun ⟨i,_⟩=>Fin.elim0 i⟩⟩
theorem star_120_213 (x:α):finiteClass (Singleton x):=by
  exact ⟨1,fun _=>x,fun y=>⟨fun h=>⟨0,h.symm⟩,fun ⟨_,h⟩=>h.symm⟩⟩
theorem star_120_214 (A B:Class α)(equiv:∀x,A x↔B x):finiteClass A↔finiteClass B:=by
  constructor
  · rintro ⟨n,f,h⟩;exact ⟨n,f,fun x=>(equiv x).symm.trans (h x)⟩
  · rintro ⟨n,f,h⟩;exact ⟨n,f,fun x=>(equiv x).trans (h x)⟩
theorem star_120_251 (A:Class α)(y:α)(h:finiteClass A):finiteClass (Insert A y):=by
  rcases h with ⟨n,f,hf⟩
  refine ⟨n+1,fun i=>if h:i.val<n then f ⟨i.val,h⟩ else y,?_⟩
  intro x;constructor
  · rintro (ha|rfl)
    · rcases (hf x).mp ha with ⟨i,rfl⟩;exact ⟨⟨i.val,Nat.lt_succ_of_lt i.isLt⟩,by simp [i.isLt]⟩
    · exact ⟨⟨n,Nat.lt_succ_self n⟩,by simp⟩
  · rintro ⟨i,hi⟩;by_cases q:i.val<n
    · left;apply (hf x).mpr;exact ⟨⟨i.val,q⟩,by simpa [q] using hi⟩
    · right;simpa [q] using hi.symm
theorem star_120_26 (φ:Class α→Prop)(A:Class α)(hA:finiteClass A)
    (h0:φ Empty)(hs:∀B x,finiteClass B→φ B→φ (Insert B x))
    (finiteInduction:∀B,finiteClass B→φ B):φ A:=finiteInduction A hA
theorem star_120_311 (a b:Nat)(h:successor a=successor b):a=b∧InductiveCardinal a:=⟨Nat.succ.inj (by simpa [successor] using h),trivial⟩
end PM.Architecture.Star120OpeningKernel
