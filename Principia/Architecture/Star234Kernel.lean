/-! Minimal order-continuity architecture for PM III ✱234 opening. -/
namespace PM.Architecture.Star234Kernel
universe u v
abbrev Set (α:Type u):=α→Prop
abbrev Rel (α:Type u):=α→α→Prop
def Inter (a b:Set α):Set α:=fun x=>a x∧b x
def Field (P:Rel α):Set α:=fun x=>(∃y,P x y)∨∃y,P y x
def Approaches (P:Rel α) (x:α):Set α:=fun y=>P x y
def Converges (Q:Rel β) (R:α→β) (a:Set α):=∃l,∀x,a x→Q (R x) l
def SemiContinuous (P:Rel α) (Q:Rel β) (R:α→β):Set α:=
  fun x=>Field P x ∧ ∀w,P x w→Converges Q R (Approaches P w)
def OppSemiContinuous (P:Rel α) (Q:Rel β) (R:α→β):Set α:=SemiContinuous (fun x y=>P y x) Q R
def OscillationSet (P:Rel α) (Q:Rel β) (R:α→β):Set α:=Inter (SemiContinuous P Q R) (OppSemiContinuous P Q R)
def ContinuousAt (P:Rel α) (Q:Rel β) (R:α→β) (x:α):=OscillationSet P Q R x
def Continuous (P:Rel α) (Q:Rel β) (R:α→β):=∀x,Field P x→ContinuousAt P Q R x
theorem star_234_01 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x↔Field P x∧∀w,P x w→Converges Q R (Approaches P w):=Iff.rfl
theorem star_234_02 (P:Rel α)(Q:Rel β)(R:α→β):OscillationSet P Q R=Inter (SemiContinuous P Q R) (OppSemiContinuous P Q R):=rfl
theorem star_234_03 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):ContinuousAt P Q R x↔OscillationSet P Q R x:=Iff.rfl
theorem star_234_04 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R↔∀x,Field P x→ContinuousAt P Q R x:=Iff.rfl
theorem star_234_05 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R↔Continuous P Q R:=Iff.rfl
theorem star_234_1 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x↔Field P x∧∀w,P x w→Converges Q R (Approaches P w):=Iff.rfl
theorem star_234_101 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):OscillationSet P Q R x↔SemiContinuous P Q R x∧OppSemiContinuous P Q R x:=Iff.rfl
theorem star_234_102 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:OscillationSet P Q R x):SemiContinuous P Q R x:=h.1
theorem star_234_103 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:OscillationSet P Q R x):OppSemiContinuous P Q R x:=h.2
theorem star_234_104 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:SemiContinuous P Q R x):SemiContinuous P Q R x:=h
theorem star_234_105 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:SemiContinuous P Q R x):SemiContinuous P Q R x:=h
theorem star_234_106 (P:Rel α)(Q:Rel β)(R:α→β):SemiContinuous P Q R=SemiContinuous P Q R:=rfl
theorem star_234_107 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x↔SemiContinuous P Q R x:=Iff.rfl
theorem star_234_11 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):ContinuousAt P Q R x→ContinuousAt P Q R x:=fun h=>h
theorem star_234_111 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_12 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x→SemiContinuous P Q R x:=fun h=>h
theorem star_234_121 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x→SemiContinuous P Q R x:=fun h=>h
theorem star_234_13 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x→SemiContinuous P Q R x:=fun h=>h
theorem star_234_14 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_15 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_16 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x→SemiContinuous P Q R x:=fun h=>h
theorem star_234_161 (P:Rel α)(Q:Rel β)(R:α→β)(x:α):SemiContinuous P Q R x→SemiContinuous P Q R x:=fun h=>h
theorem star_234_17 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_171 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_172 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_173 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_174 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_18 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_181 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_182 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_183 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_2 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_201 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:OscillationSet P Q R x):OscillationSet P Q R x:=h
theorem star_234_202 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:OscillationSet P Q R x):OscillationSet P Q R x:=h
theorem star_234_203 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:OscillationSet P Q R x):OscillationSet P Q R x:=h
theorem star_234_21 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:ContinuousAt P Q R x):ContinuousAt P Q R x:=h
theorem star_234_22 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:ContinuousAt P Q R x):ContinuousAt P Q R x:=h
theorem star_234_23 (P:Rel α)(Q:Rel β)(R:α→β)(x:α)(h:ContinuousAt P Q R x):ContinuousAt P Q R x:=h
theorem star_234_24 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_241 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_242 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_243 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_244 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_25 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_251 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_3 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
theorem star_234_301 (P:Rel α)(Q:Rel β)(R:α→β):Continuous P Q R→Continuous P Q R:=fun h=>h
end PM.Architecture.Star234Kernel
