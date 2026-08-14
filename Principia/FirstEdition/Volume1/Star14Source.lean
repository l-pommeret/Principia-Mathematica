import Principia.Syntax.DescriptionDefinitions

/- Source continuation of ✱14; reductional insertions await remote CI. -/
/- PM-VERBATIM-BEGIN PM1:✱14·02
✱14·02. E!(℩x)(φx) .=: (∃b) : φx .≡ₓ. x = b  Df
PM-VERBATIM-END PM1:✱14·02 -/
/- PM-VERBATIM-BEGIN PM1:✱14·03
✱14·03. [(℩x)(φx), (℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .=: [(℩x)(φx)] : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)}  Df
PM-VERBATIM-END PM1:✱14·03 -/
/- PM-VERBATIM-BEGIN PM1:✱14·04
✱14·04. [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .=. [(℩x)(ψx), (℩x)(φx)] . f{(℩x)(φx), (℩x)(ψx)}  Df
PM-VERBATIM-END PM1:✱14·04 -/

open PM.DescriptionSyntax
open PM.DescriptionSyntax.Formula

namespace PM.FirstEdition.Volume1.Star14Source

def star_14_02
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .sometimes vocabulary.existential (uniqueMatrix vocabulary condition)

def star_14_03
    (outerVocabulary : DescriptionVocabulary signature outerSort order)
    (innerVocabulary : DescriptionVocabulary signature innerSort order)
    (outerCondition : Formula signature realContext (outerSort :: apparentContext) order)
    (innerCondition : Formula signature realContext (innerSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (innerSort :: outerSort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope outerVocabulary outerCondition
    (.descriptionScope innerVocabulary
      (conditionUnderOuter innerCondition)
      continuation)

def star_14_04
    (laterVocabulary : DescriptionVocabulary signature laterSort order)
    (earlierVocabulary : DescriptionVocabulary signature earlierSort order)
    (laterCondition : Formula signature realContext (laterSort :: apparentContext) order)
    (earlierCondition : Formula signature realContext (earlierSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (earlierSort :: laterSort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  descriptionScopePair laterVocabulary earlierVocabulary laterCondition
    earlierCondition continuation

end PM.FirstEdition.Volume1.Star14Source

/- PM-VERBATIM-BEGIN PM1:✱14·18
✱14·18. ⊢ :: E!(℩x)(φx) .⊃ : (x) . ψx .⊃ . ψ(℩x)(φx)
Dem.
⊢.✱10·1. ⊃⊢:(x).ψ x.⊃.ψ b:
[Fact] ⊃⊢:. φ x.≡ₓ.x=b:(x).ψ x:⊃:φ x.≡ₓ.x=b:ψ b:
[✱10·11·28] ⊃⊢:. (∃ b):φ x.≡ₓ.x=b:(x).ψ x:⊃:(∃ b):φ x.≡ₓ.x=b:ψ b:.
[✱10·35] ⊃⊢:: (∃ b):φ x.≡ₓ.x=b:. (x).ψ x:. ⊃:(∃ b):φ x.≡ₓ.x=b:ψ b:.
[✱14·1·11] ⊃⊢:. E!(℩x)(φ x):(x).ψ x:⊃:ψ(℩x)(φ x):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·18 -/
/- PM-VERBATIM-BEGIN PM1:✱14·21
✱14·21. ⊢ : ψ(℩x)(φx) .⊃ . E!(℩x)(φx)
Dem.
⊢.✱14·1.⊃
⊢:. ψ{(℩x)(φ x)}. ⊃:(∃ b):φ x.≡ₓ.x=b:ψ b:
[✱10·5] ⊃:(∃ b):φ x.≡ₓ.x=b:
[✱14·11] ⊃:E!(℩x)(φ x):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·21 -/
/- PM-VERBATIM-BEGIN PM1:✱14·202
✱14·202. ⊢ : φx .≡ₓ. x = b : ≡ : (℩x)(φx) = b : ≡ : φx .≡ₓ. b = x : ≡ : b = (℩x)(φx)
Dem.
⊢.✱14·1. ⊃⊢:. (℩x)(φ x)=b. ≡:(∃ c):φ x.≡ₓ.x=c:c=b:
[✱13·195] ≡:φ x.≡ₓ.x=b:. ⊃⊢.Prop
[The second half is proved in the same way as the first half.]
PM-VERBATIM-END PM1:✱14·202 -/
/- PM-VERBATIM-BEGIN PM1:✱14·204
✱14·204. ⊢ : E!(℩x)(φx) .≡ . (∃b). (℩x)(φx) = b
Dem.
⊢.✱14·202.✱10·11.⊃
⊢:. (b):. φ x.≡ₓ.x=b:≡:(℩x)(φ x)=b:. ⊃
[✱10·281] ⊢:. (∃ b):φ x.≡ₓ.x=b:≡:(∃ b).(℩x)(φ x)=b (1)
⊢.(1).✱14·11.⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·204 -/
/- PM-VERBATIM-BEGIN PM1:✱14·205
✱14·205. ⊢ : ψ(℩x)(φx) .≡ . (∃b). b = (℩x)(φx) . ψb
PM-VERBATIM-END PM1:✱14·205 -/
/- PM-VERBATIM-BEGIN PM1:✱14·28
✱14·28. ⊢ : E!(℩x)(φx) .≡ . (℩x)(φx) = (℩x)(φx)
Dem.
⊢.✱13·15.✱4·73. ⊃⊢:. φ x.≡ₓ.x=b:≡:φ x.≡ₓ.x=b:b=b (1)
⊢.(1).✱10·11·281. ⊃
⊢:. (∃ b):φ x.≡ₓ.x=b:≡:(∃ b):φ x.≡ₓ.x=b:b=b (2)
⊢.(2).✱14·1·11. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·28 -/
/- PM-VERBATIM-BEGIN PM1:✱14·13
✱14·13. ⊢ : a = (℩x)(φx) .≡ . (℩x)(φx) = a
Dem.
⊢.✱14·1. ⊃⊢:. a=(℩x)(φ x).≡:(∃ b):φ x.≡ₓ.x=b:a=b (1)
⊢.✱13·16.✱4·36. ⊃⊢:.φ x.≡ₓ.x=b:a=b:≡:φ x.≡ₓ.x=b:b=a:
[✱10·11·281] ⊃⊢:.(∃ b):φ x.≡ₓ.x=b:a=b:
≡:(∃ b):φ x.≡ₓ.x=b:b=a:
[✱14·1] ≡:(℩x)(φ x)=a (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·13 -/
/- PM-VERBATIM-BEGIN PM1:✱14·1
✱14·1. ⊢ : [(℩x)(φx)] . ψ(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb  [✱4·2.(*14·01)]
PM-VERBATIM-END PM1:✱14·1 -/
/- PM-VERBATIM-BEGIN PM1:✱14·101
✱14·101. ⊢ : ψ(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb  [✱14·1]
PM-VERBATIM-END PM1:✱14·101 -/
/- PM-VERBATIM-BEGIN PM1:✱14·11
✱14·11. ⊢ : E!(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b  [✱4·2.(*14·02)]
PM-VERBATIM-END PM1:✱14·11 -/
/- PM-VERBATIM-BEGIN PM1:✱14·111
✱14·111. ⊢ : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .≡ : (∃b,c) : φx .≡ₓ. x = b : ψx .≡ₓ. x = c : f(b,c)
Dem.
⊢.✱4·2.(✱14·04·03).⊃
⊢::[(℩x)(ψ x)].f{(℩x)(φ x),(℩x)(ψ x)}.≡:.
[(℩x)(ψ x)]:[(℩x)(φ x)].f{(℩x)(φ x),(℩x)(ψ x)}:.
[✱14·1] ≡:.[(℩x)(ψ x)]:.(∃ b):φ x.≡ₓ.x=b:f{b,(℩x)(ψ x)}:.
[✱14·1] ≡:.(∃ c):.ψ x.≡ₓ.x=c:.(∃ b):φ x.≡ₓ.x=b:f(b,c):.
[✱11·55] ≡:.(∃ b,c):φ x.≡ₓ.x=c:ψ x.≡ₓ.x=c:f(b,c)::⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·111 -/
/- PM-VERBATIM-BEGIN PM1:✱14·112
✱14·112. ⊢ : f{(℩x)(φx), (℩x)(ψx)} .≡ : (∃b,c) : φx .≡ₓ. x = b : ψx .≡ₓ. x = c : f(b,c)
[Proof as in ✱14·111]
PM-VERBATIM-END PM1:✱14·112 -/
/- PM-VERBATIM-BEGIN PM1:✱14·113
✱14·113. ⊢ : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .≡ . f{(℩x)(φx), (℩x)(ψx)}  [✱14·111·112]
PM-VERBATIM-END PM1:✱14·113 -/
/- PM-VERBATIM-BEGIN PM1:✱14·12
✱14·12. ⊢ : E!(℩x)(φx) .⊃ : φx . φy .⊃ₓ,ᵧ. x = y
Dem.
⊢.✱14·11 ⊃⊢:.Hp.⊃:(∃ b):φ x.≡ₓ.x=b (1)
⊢.✱4·38.✱10·1.✱11·11·3. ⊃
⊢:.φ x.≡ₓ.x=b: ⊃:φ x.φ y.≡ₓ,y.x=b.y=b.
[✱13·172] ⊃ₓ,y.x=y (2)
⊢.(2).✱10·11·23. ⊃⊢:.(∃ b):φ x.≡ₓ.x=b:⊃:φ x.φ y.⊃ₓ,y.x=y (3)
⊢.(1).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·12 -/
/- PM-VERBATIM-BEGIN PM1:✱14·121
✱14·121. ⊢ : φx .≡ₓ. x = b : φx .≡ₓ. x = c : ⊃ . b = c
Dem.
⊢.✱10·1.⊃⊢:.Hp. ⊃:φ b.≡.b=b:φ b.≡.b=c:
[✱13·15] ⊃:φ b:φ b.≡.b=c:
[Ass] ⊃:b=c:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·121 -/
/- PM-VERBATIM-BEGIN PM1:✱14·122
✱14·122. ⊢ : φx .≡ₓ. x = b : ≡ : φx .⊃ₓ. x = b : φb : ≡ : φx .⊃ₓ. x = b : (∃x). φx
Dem.
⊢.✱10·22. ⊃⊢:.φ x.≡ₓ.x=b:≡:φ x.⊃ₓ.x=b:x=b.⊃ₓ.φ x:
[✱13·191] ≡:φ x.⊃ₓ.x=b:φ b (1)
⊢.✱4·71. ⊃⊢:.φ x.⊃.x=b:⊃:φ x.≡.φ x.x=b:.
[✱10·11·27] ⊃⊢:.φ x.⊃ₓ.x=b:⊃:φ x.≡ₓ.φ x.x=b:
[✱10·281] ⊃:(∃ x).φ x.≡.(∃ x).φ x.x=b.
[✱13·195] ≡.φ b (2)
⊢.(2).✱5·32. ⊃⊢:.φ x.⊃ₓ.x=b:(∃ x).φ x:≡:φ x.⊃ₓ.x=b:φ b (3)
⊢.(1).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·122 -/
/- PM-VERBATIM-BEGIN PM1:✱14·123
✱14·123. ⊢ : φ(z,w) .≡_{z,w}. z = x . w = y : ≡ : φ(z,w) .⊃_{z,w}. z = x . w = y : φ(x,y) : ≡ : φ(z,w) .⊃_{z,w}. z = x . w = y : (∃z,w). φ(z,w)
Dem.
⊢.✱11·31. ⊃⊢:.φ(z,w).≡z,w.z=x.w=y:
≡:φ(z,w).⊃z,w.z=x.w=y:z=x.w=y.⊃z,w.φ(z,w):
[✱13·21] ≡:φ(z,w).⊃z,w.z=x.w=y:φ(x,y) (1)
⊢.✱4·71. ⊃⊢:.φ(z,w).⊃.z=x.w=y:
⊃:φ(z,w).≡.φ(z,w).z=x.w=y:.
[✱11·11·32] ⊃⊢:.φ(z,w).⊃z,w.z=x.w=y:
⊃:φ(z,w).≡z,w.φ(z,w).z=x.w=y:
[✱11·341] ⊃:(∃ z,w).φ(z,w).≡.(∃ z,w).φ(z,w).z=x.w=y.
[✱13·22] ≡.φ(x,y) (2)
⊢.(2).✱5·32. ⊃⊢:.φ(z,w).⊃z,w.z=x.w=y:(∃ z,w).φ(z,w):
≡:φ(z,w).⊃z,w.z=x.w=y:φ(x,y) (3)
⊢.(1).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·123 -/
/- PM-VERBATIM-BEGIN PM1:✱14·124
✱14·124. ⊢ : (∃x,y) : φ(z,w) .≡_{z,w}. z = x . w = y : ≡ : (∃x,y). φ(x,y) : φ(z,w) . φ(u,v) .⊃_{z,w,u,v}. z = u . w = v
Dem.
⊢.✱14·123.✱3·27. ⊃ ⊢:.(∃ x,y):φ(z,w).≡z,w.z=x.w=y:⊃.(∃ x,y).φ(x,y) (1)
⊢.✱11·1.✱3·47. ⊃⊢:.φ(z,w).≡z,w.z=x.w=y:
⊃:φ(z,w).φ(u,v).⊃.z=x.w=y.u=x.v=y.
[✱13·172] ⊃.z=u.w=v (2)
⊢.(2).✱11·11·35.⊃
⊢:.(∃ x,y):φ(z,w).≡z,w.z=x.w=y:
⊃:φ(z,w).φ(u,v).⊃.z=u.w=v (3)
⊢.(3).✱11·11·3.⊃
⊢:.(∃ x,y):φ(z,w).≡z,w.z=x.w=y:
⊃:φ(z,w).φ(u,v).⊃z,w,u,v.z=u.w=v (4)
⊢.✱11·1. ⊃⊢:.φ(x,y):φ(z,w).φ(u,v).⊃z,w,u,v.z=u.w=v:
⊃:φ(x,y):φ(z,w).φ(x,y).⊃z,w.z=x.w=y:
[✱5·33] ⊃:φ(x,y):φ(z,w).⊃z,w.z=x.w=y:
[✱14·123] ⊃:φ(z,w).≡z,w.z=x.w=y (5)
⊢.(5).✱11·11·34·45.⊃
⊢:.(∃ x,y).φ(x,y):φ(z,w).φ(u,v).⊃z,w,u,v.z=u.w=v:
⊃:(∃ x,y):φ(z,w).≡z,w.z=x.w=y (6)
⊢.(1).(4).(6). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·124 -/
/- PM-VERBATIM-BEGIN PM1:✱14·131
✱14·131. ⊢ : (℩x)(φx) = (℩x)(ψx) .≡ . (℩x)(ψx) = (℩x)(φx)
Dem.
⊢.✱14·1. ⊃⊢::(℩x)(φ x)=(℩x)(ψ x).≡:.(∃ b):φ x.≡ₓ.x=b:b=(℩x)(ψ x):.
[✱14·1] ≡:.(∃ b):.φ x.≡ₓ.x=b:.(∃ c):ψ x.≡ₓ.x=c:b=c:.
[✱11·6] ≡:. (∃ c):. ψ x.≡ₓ.x=c:. (∃ b):φ x.≡ₓ.x=b:b=c:.
[✱14·1] ≡:. (∃ c):. ψ x.≡ₓ.x=c:(℩x)(φ x)=c:.
[✱14·13] ≡:. (∃ c):. ψ x.≡ₓ.x=c:c=(℩x)(φ x):.
[✱14·1] ≡:. (℩x)(ψ x)=(℩x)(φ x):: ⊃⊢.Prop
The above proposition may also be proved as follows:
⊢.✱14·111.⊃⊢:. (℩x)(φ x) =(℩x)(ψ x).
≡:(∃ b,c):φ x.≡ₓ.x=b:ψ x.≡ₓ.x=c:b=c:
[✱4·3.✱13·6.✱11·11·341] ≡:(∃ b,c):ψ x.≡ₓ.x=c:φ x.≡ₓ.x=b:c=b:
[✱11·2.✱14·111] ≡:(℩x)(ψ x)=(℩x)(φ x):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·131 -/
/- PM-VERBATIM-BEGIN PM1:✱14·14
✱14·14. ⊢ : a = b . b = (℩x)(φx) .⊃ . a = (℩x)(φx)  [✱13·13]
PM-VERBATIM-END PM1:✱14·14 -/
/- PM-VERBATIM-BEGIN PM1:✱14·142
✱14·142. ⊢ : a = (℩x)(φx) . (℩x)(φx) = (℩x)(ψx) .⊃ . a = (℩x)(ψx)
Dem.
⊢.✱14·1. ⊃⊢:: Hp.⊃:. (∃ b):φ x.≡ₓ.x=b:a=b:.
(∃ c):φ x.≡ₓ.x=c:c=(℩x)(ψ x):.
[✱13·195] ⊃:. φ x.≡ₓ.x=a:. (∃ c):φ x.≡ₓ.x=c:c=(℩x)(ψ x):.
[✱10·35] ⊃:. (∃ c):. φ x.≡ₓ.x=a:φ x.≡ₓ.x=c:c=(℩x)(ψ x):.
[✱14·121] ⊃:. (∃ c):. φ x.≡ₓ.x=a:a=c:c=(℩x)(ψ x):.
[✱3·27.✱13·195] ⊃:. a=(℩x)(φ x):: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·142 -/
/- PM-VERBATIM-BEGIN PM1:✱14·144
✱14·144. ⊢ : (℩x)(φx) = (℩x)(ψx) . (℩x)(ψx) = (℩x)(χx) .⊃ . (℩x)(φx) = (℩x)(χx)
Dem.
⊢.✱14·111. ⊃⊢:: Hp.⊃:. (∃ a,b):φ x.≡ₓ.x=a:ψ x.≡ₓ.x=b:a=b:.
(∃ c,d):ψ x.≡ₓ.x=c:χ x.≡ₓ.x=d:c=d:.
[✱13·195] ⊃:. (∃ a):φ x.≡ₓ.x=a:ψ x.≡ₓ.x=a:.
(∃ c):ψ x.≡ₓ.x=c:χ x.≡ₓ.x=c:.
[✱11·54] ⊃:. (∃ a,c):φ x.≡ₓ.x=a:ψ x.≡ₓ.x=a:
ψ x.≡ₓ.x=c:χ x.≡ₓ.x=c:.
[✱14·121.✱11·42] ⊃:. (∃ a,c):φ x.≡ₓ.x=a:χ x.≡ₓ.x=c:a=c:.
[✱14·111] ⊃:. (℩x)(φ x)=(℩x)(χ x):: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·144 -/
/- PM-VERBATIM-BEGIN PM1:✱14·145
✱14·145. ⊢ : a = (℩x)(φx) . a = (℩x)(ψx) .⊃ . (℩x)(φx) = (℩x)(ψx)
Dem.
⊢.✱14·1. ⊃⊢:. a=(℩x)(φ x). ≡:(∃ b):φ x.≡ₓ.x=b:a=b:
[✱13·195] ≡:φ x.≡ₓ.x=a (1)
⊢ . (1) . ✱14·1. ⊃ ⊢ :: Hp . ≡ :. φ x . ≡ₓ . x = a :. (∃ b) : ψ x . ≡ₓ. x = b : a = b :.
[✱10·35] ≡ :. (∃ b) :. φ x . ≡ₓ . x = a : ψ x . ≡ₓ . x = b : a = b :.
[✱14·111] ⊃ :. (℩x)(φ x) = (℩x)(ψ x) :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱14·145 -/
/- PM-VERBATIM-BEGIN PM1:✱14·15
✱14·15. ⊢ : (℩x)(φx) = b .⊃ : ψ{(℩x)(φx)} .≡ . ψb
Dem.
⊢ . ✱14·1. ⊃
⊢ :: Hp . ⊃ :. (∃ c) : φ x . ≡ₓ . x = c : c = b :.
[✱13·195] ⊃ :. φ x . ≡ₓ . x ≡ b (1)
⊢ . (1) . ✱14·1. ⊃
⊢ :: Hp . ⊃ :. ψ {(℩x)(φ x)} . ≡ : (∃ c) : x = b . ≡ₓ . x = c : ψ c :
[✱13·192] ≡ : ψ b :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱14·15 -/
/- PM-VERBATIM-BEGIN PM1:✱14·16
✱14·16. ⊢ : (℩x)(φx) = (℩x)(ψx) .⊃ : χ{(℩x)(φx)} .≡ . χ{(℩x)(ψx)}
Dem.
⊢ .✱14·1. ⊃ ⊢ :. Hp. ⊃ : (∃ b) : φ x . ≡ₓ . x = b : b = (℩x)(ψ x) (1)
⊢ .✱14·1. ⊃ ⊢ :: φ x . ≡ₓ . x = b : ⊃ :.
χ {(℩x)(φ x)} . ≡ : (∃ c) : x = b . ≡ₓ . x = c : χ c :
[✱13·192] ≡ : χ b (2)
⊢ . ✱14·13·15. ⊃ ⊢ :. b = (℩x)(ψ x) . ⊃ : χ b . ≡ . χ {(℩x)(ψ x)} (3)
⊢ .(2) . (3). ⊃ ⊢ :. φ x . ≡ₓ . x = b : b = (℩x)(ψ x) :
⊃ : χ {(℩x)(φ x)} . ≡ . χ {(℩x)(ψ x)} (4)
⊢ . (1) . (4) . ✱10·1·23. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱14·16 -/
/- PM-VERBATIM-BEGIN PM1:✱14·17
✱14·17. ⊢ : (℩x)(φx) = b .≡ : ψ!(℩x)(φx) .≡_ψ . ψ!b
Dem.
⊢ .✱14·15 . ✱10·11·21. ⊃
⊢ :. (℩x)(φ x) = b . ⊃ : ψ ! (℩x)(φ x) . ≡_ψ . ψ ! b (1)
⊢ .✱10·1 . ✱4·22. ⊃ ⊢ :: χ ! x . ≡ₓ . x = b : ψ ! (℩x)(φ x) . ≡_ψ . ψ ! b :
⊃ : (℩x)(φ x) = b . ≡ . b = b :
[✱13·15] ⊃ : (℩x)(φ x) = b (2)
⊢ .(2) . Exp. ✱10·11·23 . ⊃
⊢ :: (∃ χ) : χ ! x . ≡ₓ . x = b : ⊃ :. ψ ! (℩x)(φ x) . ≡_ψ . ψ ! b : ⊃ . (℩x)(φ x) = b (3)
⊢ . ✱12·1. ⊃ ⊢ : (∃ χ) : χ ! x . ≡ₓ . x = b (4)
⊢ .(3) . (4). ⊃ ⊢ :. ψ ! (℩x)(φ x) . ≡_ψ .ψ ! b : ⊃ . (℩x)(φ x) = b (5)
⊢ .(1) . (5). ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱14·17 -/
/- PM-VERBATIM-BEGIN PM1:✱14·171
✱14·171. ⊢ : (℩x)(φx) = b .≡ : ψ!b .⊃_ψ . ψ!(℩x)(φx)
Dem.
⊢.✱14·17. ⊃⊢:. (℩x)(φ x)=b.⊃:ψ!b.⊃_ψ.ψ!(℩x)(φ x) (1)
⊢.✱10·1.✱12·1. ⊃⊢:. ψ!b.⊃_ψ.ψ!(℩x)(φ x):⊃:b=b.⊃.(℩x)(φ x)=b:
[✱13·15] ⊃:(℩x)(φ x)=b (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·171 -/
/- PM-VERBATIM-BEGIN PM1:✱14·2
✱14·2. ⊢ . (℩x)(x = a) = a
Dem.
⊢.✱14·101. ⊃⊢:. (℩x)(x=a)=a.≡:(∃ b):x=a.≡ₓ.x=b:b=a:
[✱13·195] ≡:x=a.≡ₓ.x=a (1)
⊢.(1).Id. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·2 -/
/- PM-VERBATIM-BEGIN PM1:✱14·201
✱14·201. ⊢ : E!(℩x)(φx) .⊃ . (∃x). φx
Dem.
⊢.✱14·11. ⊃⊢:. Hp.⊃:(∃ b):φ x.≡ₓ.x=b:
[✱10·1] ⊃:(∃ b):φ b.≡.b=b:
[✱13·15] ⊃:(∃ b).φ b:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·201 -/
/- PM-VERBATIM-BEGIN PM1:✱14·203
✱14·203. ⊢ : E!(℩x)(φx) .≡ : (∃x). φx : φx . φy .⊃ₓ,ᵧ. x = y
Dem.
⊢.✱14·12·201. ⊃⊢:. E!(℩x)(φ x).⊃:(∃ x).φ x:φ x.φ y.⊃ₓ,y.x=y (1)
⊢.✱10·1. ⊃⊢:. φ b:φ x.φ y.⊃ₓ,y.x=y:⊃:φ b:φ x.φ b.⊃ₓ.x=b:
[✱5·33] ⊃:φ b:φ x.⊃ₓ.x=b:
[✱13·191] ⊃:x=b.⊃ₓ.φ x:
φ x.⊃ₓ.x=b:
[✱10·22] ⊃:φ x.≡ₓ.x=b (2)
⊢.(2).✱10·1·28. ⊃⊢:. (∃ b):φ b:φ x.φ y.⊃ₓ,y.x=y:⊃:(∃ b):φ x.≡ₓ.x=b:.
[✱10·35] ⊃⊢:. (∃ b).φ b:φ x.φ y.⊃ₓ,y.x=y:⊃:(∃ b):φ x.≡ₓ.x=b:
[✱14·11] ⊃:E!(℩x)(φ x) (3)
⊢.(1).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·203 -/
/- PM-VERBATIM-BEGIN PM1:✱14·22
✱14·22. ⊢ : E!(℩x)(φx) .≡ . φ(℩x)(φx)
Dem.
⊢.✱14·122. ⊃⊢:. φ x.≡ₓ.x=b:⊃.φ b (1)
⊢.(1).✱4·71. ⊃⊢:. φ x.≡ₓ.x=b:≡:φ x.≡ₓ.x=b:φ b:.
[✱10·11·281] ⊃⊢:. (∃ b):φ x.≡ₓ.x=b:≡:(∃ b):φ x.≡ₓ.x=b:φ b:.
[✱14·11·101] ⊃⊢:E!(℩x)(φ x).≡.φ(℩x)(φ x):⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·22 -/
/- PM-VERBATIM-BEGIN PM1:✱14·23
✱14·23. ⊢ : E!(℩x)(φx . ψx) .≡ . φ{(℩x)(φx . ψx)}
Dem.
⊢.✱14·22. ⊃⊢:. E!(℩x)(φ x.ψ x).
≡:[(℩x)(φ x.ψ x)]:φ {(℩x)(φ x.ψ x)}ψ {(℩x)(φ x.ψ x)}
[✱10·5.✱3·26] ⊃:φ{(℩x)(φ x.ψ x)} (1)
⊢.✱14·21. ⊃⊢:φ {(℩x)(φ x.ψ x)}.⊃.E!(℩x)(φ x.ψ x) (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·23 -/
/- PM-VERBATIM-BEGIN PM1:✱14·24
✱14·24. ⊢ : E!(℩x)(φx) .≡ : [(℩x)(φx)] : φy .≡ᵧ. y = (℩x)(φx)
Dem.
⊢.✱14·1.⊃⊢:. [(℩x)(φ x)]:φ y. ≡y.y=(℩x)(φ x):
≡:(∃ b):φ y.≡y.y=b:φ y.≡y.y=b:
[✱4·24.✱10·281] ≡:(∃ b):φ y.≡y.y=b:
[✱14·11] ≡:E!(℩x)(φ x):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·24 -/
/- PM-VERBATIM-BEGIN PM1:✱14·241
✱14·241. ⊢ : E!(℩x)(φx) .⊃ : φy .≡ᵧ. y = (℩x)(φx)
Dem.
⊢.✱14·203. ⊃⊢:: Hp.⊃:. φ y.φ x.⊃.y=x:.
[Exp] ⊃:. φ y.⊃:φ x.⊃.y=x::
[✱10·11·21] ⊃⊢:: Hp.⊃:. φ y.⊃:φ x.⊃ₓ.y=x:.
[✱4·71] ⊃:. φ y. ≡:φ y:φ x.⊃ₓ.y=x:
[✱13·191] ≡:y=x.⊃ₓ.φ x:φ x.⊃ₓ.y=x:
[✱10·22] ≡:φ x.≡ₓ.y=x
[✱14·202] ≡:y=(℩x)(φ x):: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·241 -/
/- PM-VERBATIM-BEGIN PM1:✱14·242
✱14·242. ⊢ : φx .≡ₓ. x = b : ⊃ : ψb .≡ . ψ(℩x)(φx)  [✱14·202·15]
PM-VERBATIM-END PM1:✱14·242 -/
/- PM-VERBATIM-BEGIN PM1:✱14·25
✱14·25. ⊢ : E!(℩x)(φx) .⊃ : φx ⊃ₓ ψx .≡ . ψ(℩x)(φx)
Dem.
⊢.✱4·84.✱10·27·271.⊃⊢:: φ x. ≡ₓ.x=b:⊃:. φ x⊃ₓψ x.≡:x=b.⊃ₓ.ψ x:
[✱13·191] ≡:ψ b:
[✱14·242] ≡.ψ(℩x)(φ x) (1)
⊢.(1).✱10·11·23. ⊃⊢:. (∃ b):φ x.≡ₓ.x=b:
⊃:φ x⊃ₓψ x.≡.ψ(℩x)(φ x) (2)
⊢.(2).✱14·11. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·25 -/
/- PM-VERBATIM-BEGIN PM1:✱14·26
✱14·26. ⊢ : E!(℩x)(φx) .⊃ : (∃x). φx . ψx .≡ . ψ{(℩x)(φx)} .≡ . φx ⊃ₓ ψx
Dem.
⊢.✱14·11.⊃
⊢:. Hp. ⊃:(∃ b):φ x.≡ₓ.x=b (1)
⊢.✱10·311. ⊃⊢:: φ x.≡ₓ.x=b:⊃:. φ x.ψ x.≡ₓ.x=b.ψ x:.
[✱10·281] ⊃:. (∃ x).φ x.ψ x.≡.(∃ x).x=b.ψ x.
[✱13·195] ≡.ψ b
[✱14·242] ≡.ψ {(℩x)(φ x)} (2)
⊢.(2).✱10·11·23.⊃
⊢:. (∃ b):φ x.≡ₓ.x=b: ⊃:(∃ x).φ x.ψ x.≡.ψ {(℩x)(φ x)} (3)
⊢.(1).(3).✱14·25.⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·26 -/
/- PM-VERBATIM-BEGIN PM1:✱14·27
✱14·27. ⊢ : E!(℩x)(φx) .⊃ : φx ≡ₓ ψx .≡ . (℩x)(φx) = (℩x)(ψx)
Dem.
⊢.✱4·86·21. ⊃⊢:: φ x.≡ₓ.x=b:⊃:. φ x.≡.ψ x:≡:ψ x.≡.x=b (1)
⊢.(1).✱10·11·27. ⊃⊢:: φ x.≡ₓ.x=b:⊃:. (x):. φ x.≡.ψ x:≡:ψ x.≡.x=b:.
[✱10·271] ⊃:. φ x.≡ₓ.ψ x:≡:ψ x.≡ₓ.x=b:
[✱14·202] ≡:b=(℩x)(ψ x)
[✱14·242] ≡:(℩x)(φ x)=(℩x)(ψ x) (2)
⊢.(2).✱10·11·23.✱14·11. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·27 -/
/- PM-VERBATIM-BEGIN PM1:✱14·271
✱14·271. ⊢ : φx .≡ₓ. ψx .⊃ : E!(℩x)(φx) .≡ . E!(℩x)(ψx)
Dem.
⊢.✱4·86. ⊃⊢:: φ x≡ψ x.⊃:. φ x.≡.x=b:≡:ψ x.≡.x=b::
[✱10·11·27] ⊃⊢:: Hp.⊃:. (x):. φ x.≡.x=b:≡:ψ x.≡.x=b:.
[✱10·271] ⊃:. (x):φ x.≡.x=b:≡:(x):ψ x.≡.x=b::
[✱10·11·21] ⊃⊢:: Hp.⊃:. (b):. φ x.≡ₓ.x=b:≡:ψ x.≡ₓ.x=b:.
[✱10·281] ⊃:. (∃ b):φ x.≡ₓ.x=b:≡:(∃ b):ψ x.≡ₓ.x=b::
⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·271 -/
/- PM-VERBATIM-BEGIN PM1:✱14·272
✱14·272. ⊢ : φx .≡ₓ. ψx .⊃ : χ(℩x)(φx) .≡ . χ(℩x)(ψx)
Dem.
⊢.✱4·86. ⊃⊢:: φ x≡ψ x.⊃:. φ x.≡.x=b:≡:ψ x.≡.x=b:.
[✱10·11·414] ⊃⊢:: Hp. ⊃:. φ x.≡ₓ.x=b:≡:ψ x.≡ₓ.x=b:.
[Fact] ⊃:. φ x.≡ₓ.x=b:χ b:≡:ψ x.≡ₓ.x=b:χ b:.
[✱10·11·21] ⊃⊢:: Hp.⊃:. (b):. φ x.≡ₓ.x=b:χ b:≡:ψ x.≡ₓ.x=b:χ b:.
[✱10·281] ⊃:. (∃ b):. φ x.≡ₓ.x=b:χ b:≡
:(∃ b):ψ x.≡ₓ.x=b:χ b:.
[✱14·101] ⊃:. χ(℩x)(φ x).≡.χ(℩x)(ψ x):: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·272 -/
/- PM-VERBATIM-BEGIN PM1:✱14·3
✱14·3. ⊢ : p ≡ q .⊃ₚ,ᵩ. f(p) ≡ f(q) : E!(℩x)(φx) .⊃ : f{[(℩x)(φx)] . χ(℩x)(φx)} .≡ . [(℩x)(φx)] . f{χ(℩x)(φx)}
Dem.
⊢.✱14·242.⊃
⊢:. φ x.≡ₓ.x=b:⊃:[(℩x)(φ x)].χ(℩x)(φ x).≡.χ b (1)
⊢.(1).⊃⊢:. p≡ q.⊃ₚ,q.f(p)≡ f(q):φ x.≡ₓ.x=b:⊃:
f{[(℩x)(φ x)].χ(℩x)(φ x)}.≡.f(χ b) (2)
⊢.✱14·242.⊃
⊢:. φ x.≡ₓ.x=b:⊃:[(℩x)(φ x)].f{χ(℩x)(φ x)}.≡.f(χ b) (3)
⊢.(2).(3).⊃
⊢:. p≡ q.⊃ₚ,q.f(p)≡ f(q):φ x.≡ₓ.x=b:⊃:
f{[(℩x)(φ x)].χ(℩x)(φ x)}.≡.[(℩x)(φ x)].f{χ(℩x)(φ x)} (4)
⊢.(4).✱10·23.✱14·11.⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·3 -/
/- PM-VERBATIM-BEGIN PM1:✱14·31
✱14·31. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ∨ χ(℩x)(φx) .≡ : p ∨ [(℩x)(φx)] . χ(℩x)(φx)
Dem.
⊢.✱14·242. ⊃⊢:. φ x.≡ₓ.x=b:⊃:[(℩x)(φ x)].p∨χ(℩x)(φ x).≡.p∨χ b (1)
⊢.✱14·242. ⊃⊢:. φ x.≡ₓ.x=b:⊃:[(℩x)(φ x)].χ(℩x)(φ x).≡.χ b:
[✱4·37] ⊃:p∨[(℩x)(φ x)]χ(℩x)(φ x).≡.p∨χ b (2)
⊢.(1).(2). ⊃⊢:. φ x.≡ₓ.x=b:⊃:[(℩x)(φ x)].p∨χ(℩x)(φ x).
≡.p∨[(℩x)(φ x)]χ(℩x)(φ x) (3)
⊢.(3).✱10·23.✱14·11. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·31 -/
/- PM-VERBATIM-BEGIN PM1:✱14·32
✱14·32. ⊢ : E!(℩x)(φx) .≡ : [(℩x)(φx)] . ∼χ(℩x)(φx) .≡ . ∼[(℩x)(φx)] . χ(℩x)(φx)
[✱14·242.✱4·11.✱10·23.✱14·11]
PM-VERBATIM-END PM1:✱14·32 -/
/- PM-VERBATIM-BEGIN PM1:✱14·33
✱14·33. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ⊃ χ(℩x)(φx) .≡ : p .⊃ . [(℩x)(φx)] . χ(℩x)(φx)
[✱14·242.✱4·85.✱10·23.✱14·11]
PM-VERBATIM-END PM1:✱14·33 -/
/- PM-VERBATIM-BEGIN PM1:✱14·331
✱14·331. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . χ(℩x)(φx) ⊃ p .≡ : [(℩x)(φx)] . χ(℩x)(φx) .⊃ . p
[✱4·84.✱14·242.✱10·23.✱14·11]
PM-VERBATIM-END PM1:✱14·331 -/
/- PM-VERBATIM-BEGIN PM1:✱14·332
✱14·332. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ≡ χ(℩x)(φx) .≡ : p .≡ . [(℩x)(φx)] . χ(℩x)(φx)
[✱4·86.✱14·242.✱10·23.✱14·11]
PM-VERBATIM-END PM1:✱14·332 -/
/- PM-VERBATIM-BEGIN PM1:✱14·34
✱14·34. ⊢ : p : [(℩x)(φx)] . χ(℩x)(φx) .≡ : [(℩x)(φx)] : p . χ(℩x)(φx)
Dem.
⊢.✱14·1.⊃
⊢:. p:[(℩x)(φ x)].χ (℩x)(φ x):≡:p:(∃ b):φ x. ≡ₓ.x=b:χ b:
[✱10·35] ≡:(∃ b):p:φ x.≡ₓ.x=b:χ b:
[✱14·1] ≡:[(℩x)(φ x)]:p.χ(℩x)(φ x):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱14·34 -/
