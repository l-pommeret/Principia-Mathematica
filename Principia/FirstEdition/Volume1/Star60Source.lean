/-!
# PM I, ✱60 — The Sub-Classes of a Given Class
Project Gutenberg 78050, printed pp. 406–411.  The numbered formulas are
preserved below; prose demonstrations remain in the canonical witness.
-/
/- PM-VERBATIM-BEGIN PM1:✱60·01
✱60·01. Cl = κ̂α̂{κ = β̂(β ⊂ α)} Df
PM-VERBATIM-END PM1:✱60·01 -/
/- PM-VERBATIM-BEGIN PM1:✱60·02
✱60·02. Cl ex = κ̂α̂{κ = β̂(β ⊂ α . ∃!β)} Df
PM-VERBATIM-END PM1:✱60·02 -/
/- PM-VERBATIM-BEGIN PM1:✱60·03
✱60·03. Cls² = ClʻCls Df
PM-VERBATIM-END PM1:✱60·03 -/
/- PM-VERBATIM-BEGIN PM1:✱60·04
✱60·04. Cls³ = ClʻCls² Df
PM-VERBATIM-END PM1:✱60·04 -/
/- PM-VERBATIM-BEGIN PM1:✱60·1
✱60·1. ⊢ : κ Cl α .≡. κ = β̂(β ⊂ α)
PM-VERBATIM-END PM1:✱60·1 -/
/- PM-VERBATIM-BEGIN PM1:✱60·11
✱60·11. ⊢ : κ Cl ex α .≡. κ = β̂(β ⊂ α . ∃!β)
PM-VERBATIM-END PM1:✱60·11 -/
/- PM-VERBATIM-BEGIN PM1:✱60·12
✱60·12. ⊢ . Clʻα = β̂(β ⊂ α)
PM-VERBATIM-END PM1:✱60·12 -/
/- PM-VERBATIM-BEGIN PM1:✱60·13
✱60·13. ⊢ . Cl exʻα = β̂(β ⊂ α . ∃!β)
PM-VERBATIM-END PM1:✱60·13 -/
/- PM-VERBATIM-BEGIN PM1:✱60·14
✱60·14. ⊢ . ∃!Clʻα
PM-VERBATIM-END PM1:✱60·14 -/
/- PM-VERBATIM-BEGIN PM1:✱60·15
✱60·15. ⊢ . ∃!Cl exʻα
PM-VERBATIM-END PM1:✱60·15 -/
/- PM-VERBATIM-BEGIN PM1:✱60·2
✱60·2. ⊢ : β ∈ Clʻα .≡. β ⊂ α
PM-VERBATIM-END PM1:✱60·2 -/
/- PM-VERBATIM-BEGIN PM1:✱60·21
✱60·21. ⊢ : β ∈ Cl exʻα .≡. β ⊂ α . ∃!β
PM-VERBATIM-END PM1:✱60·21 -/
/- PM-VERBATIM-BEGIN PM1:✱60·22
✱60·22. ⊢ : β ∈ Cl exʻα .≡. β ∈ Clʻα . ∃!β
PM-VERBATIM-END PM1:✱60·22 -/
/- PM-VERBATIM-BEGIN PM1:✱60·23
✱60·23. ⊢ : β ∈ Cl exʻα .≡. β ∈ Clʻα − ιʻΛ
PM-VERBATIM-END PM1:✱60·23 -/
/- PM-VERBATIM-BEGIN PM1:✱60·24
✱60·24. ⊢ . Cl exʻα = Clʻα − ιʻΛ
PM-VERBATIM-END PM1:✱60·24 -/
/- PM-VERBATIM-BEGIN PM1:✱60·3
✱60·3. ⊢ . Λ ∈ Clʻα
PM-VERBATIM-END PM1:✱60·3 -/
/- PM-VERBATIM-BEGIN PM1:✱60·31
✱60·31. ⊢ . ∃!Clʻα
PM-VERBATIM-END PM1:✱60·31 -/
/- PM-VERBATIM-BEGIN PM1:✱60·32
✱60·32. ⊢ . ClʻΛ = ιʻΛ
Dem.
⊢.*60·2.*24·13.⊃⊢:α∈ClʻΛ. ≡.α=Λ.
[*51·15] ≡.α∈ιʻΛ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·32 -/
/- PM-VERBATIM-BEGIN PM1:✱60·321
✱60·321. ⊢ : α = Λ .≡. Clʻα = ιʻα
Dem.
⊢.*60·32. ⊃⊢:α=Λ.⊃.Clʻ α=ιʻ α (1)
⊢.*60·2.*51·15.⊃
⊢:.Clʻ α=ιʻ α.≡:β⊂ α.≡_β.β=α:
[*10·1] ⊃:Λ⊂ α.≡.Λ=α:
[*24·12] ⊃:Λ=α (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·321 -/
/- PM-VERBATIM-BEGIN PM1:✱60·33
✱60·33. ⊢ . Cl exʻΛ = Λ ∩ Cls
Dem.
⊢.*60·22·32.⊃⊢:β∈Cl exʻΛ. ≡.β∈ιʻΛ.∃ !β.
[*51·15.*24·54] ≡.β=Λ.β≠Λ (1)
⊢.(1).*3·24.⊃⊢.β∼∈Cl exʻΛ (2)
⊢.(2).*10·11.*24·15.⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·33 -/
/- PM-VERBATIM-BEGIN PM1:✱60·34
✱60·34. ⊢ . α ∈ Clʻα
PM-VERBATIM-END PM1:✱60·34 -/
/- PM-VERBATIM-BEGIN PM1:✱60·35
✱60·35. ⊢ : ∃!α .⊃. α ∈ Cl exʻα
PM-VERBATIM-END PM1:✱60·35 -/
/- PM-VERBATIM-BEGIN PM1:✱60·36
✱60·36. ⊢ : ∃!α .⊃. ∃!Cl exʻα
PM-VERBATIM-END PM1:✱60·36 -/
/- PM-VERBATIM-BEGIN PM1:✱60·361
✱60·361. ⊢ : ∃!α .≡. ∃!Cl exʻα
PM-VERBATIM-END PM1:✱60·361 -/
/- PM-VERBATIM-BEGIN PM1:✱60·362
✱60·362. ⊢ . Clʻιʻx = ιʻΛ ∪ ιʻιʻx
PM-VERBATIM-END PM1:✱60·362 -/
/- PM-VERBATIM-BEGIN PM1:✱60·37
✱60·37. ⊢ . Cl exʻιʻx = ιʻιʻx
Dem.
⊢.*60·21.⊃⊢:β∈Cl exʻιʻ x. ≡.β⊂ ιʻ x.∃ !β.
[*51·4] ≡.β=ιʻ x.
[*51·15] ≡.β∈ ιʻ ιʻ x:⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·37 -/
/- PM-VERBATIM-BEGIN PM1:✱60·371
✱60·371. ⊢ : α ∈ 1 .⊃. Clʻα ⊂ 0 ∪ 1
Dem.
⊢.*51·401.⊃⊢:: α=ιʻ x. ⊃:. β⊂ α.≡:β=Λ.∨.β=ιʻ x:
[*54·102.*52·22] ⊃:β∈ 0.∨.β∈ 1:.
[*60·2.*22·34] ⊃:. β∈Clʻ α.⊃.β∈ 0∪ 1 (1)
⊢.(1).*10·11·23.*52·1. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·371 -/
/- PM-VERBATIM-BEGIN PM1:✱60·38
✱60·38. ⊢ . Clʻ(ιʻx ∪ ιʻy) = ιʻΛ ∪ ιʻιʻx ∪ ιʻιʻy ∪ ιʻ(ιʻx ∪ ιʻy)
Dem.
⊢.*60·37. ⊃⊢:α=ιʻ x.⊃.Cl exʻα=ιʻ α:
[*10·11·23] ⊃⊢:(∃ x).α=ιʻ x.⊃.Cl exʻα=ιʻ α:
[*52·1] ⊃⊢:α∈ 1.⊃.Cl exʻα=ιʻ α (1)
⊢.*60·361.*51·161. ⊃⊢:Cl exʻα=ιʻ α.⊃.∃ !α (2)
⊢.*60·21.*10·1. ⊃⊢:.Cl exʻα=ιʻ α. ⊃:ιʻ x⊂ α.∃ !ιʻ x.∃.ιʻ x=α:
[*51·161] ⊃:ιʻ x⊂ α.≡.ιʻ x=α:
[*51·2] ⊃:x∈α.≡.ιʻ x=α (3)
⊢.(3).*10·11·21·281.⊃⊢:.Cl exʻ α=ιʻα.⊃:∃ !α. ≡.(∃ x).ιʻ x=α.
[*52·1] ≡.α∈ 1:
[(2)] ⊃:α∈ 1 (4)
⊢.(1).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·38 -/
/- PM-VERBATIM-BEGIN PM1:✱60·39
✱60·39. ⊢ : α ∈ 2 .⊃. Clʻα ⊂ 0 ∪ 1 ∪ 2
PM-VERBATIM-END PM1:✱60·39 -/
/- PM-VERBATIM-BEGIN PM1:✱60·391
✱60·391. ⊢ : β ∈ Clʻα . γ ⊂ β .⊃. γ ∈ Clʻα
PM-VERBATIM-END PM1:✱60·391 -/
/- PM-VERBATIM-BEGIN PM1:✱60·4
✱60·4. ⊢ : β ∈ Clʻα .⊃. β ∩ γ ∈ Clʻα
PM-VERBATIM-END PM1:✱60·4 -/
/- PM-VERBATIM-BEGIN PM1:✱60·41
✱60·41. ⊢ : β ∈ Clʻα . γ ⊂ β . ∃!γ .⊃. γ ∈ Cl exʻα
PM-VERBATIM-END PM1:✱60·41 -/
/- PM-VERBATIM-BEGIN PM1:✱60·42
✱60·42. ⊢ : β,γ ∈ Clʻα .≡. β ∪ γ ∈ Clʻα
PM-VERBATIM-END PM1:✱60·42 -/
/- PM-VERBATIM-BEGIN PM1:✱60·43
✱60·43. ⊢ : β ∈ Clʻα . γ ∈ Cl exʻα .⊃. β ∪ γ ∈ Cl exʻα
PM-VERBATIM-END PM1:✱60·43 -/
/- PM-VERBATIM-BEGIN PM1:✱60·44
✱60·44. ⊢ : ρ ∈ Clʻ(α ∪ β) .≡. (∃γ,δ).γ ∈ Clʻα . δ ∈ Clʻβ . ρ = γ ∪ δ
PM-VERBATIM-END PM1:✱60·44 -/
/- PM-VERBATIM-BEGIN PM1:✱60·45
✱60·45. ⊢ . sʻClʻα = α
Dem.
⊢.*60·2.*2·621·68.⊃
⊢:ρ∈Clʻ (α∪β). ⊃.ρ=(ρ∩α)∪ (ρ∩β) (1)
⊢.*60·2.*22·43. ⊃⊢.ρ∩ α∈Clʻ α.ρ∩ β∈Clʻβ (2)
⊢.(1).(2).*10·24.⊃
⊢:ρ∈Clʻ (α∪β). ⊃.(∃ γ,δ).γ∈Clʻ α.δ∈Clʻ β.ρ=γ∪δ (3)
⊢.*60·2.⊃
⊢:(∃ γ,δ).γ∈Clʻ α.δ∈Clʻβ.ρ=γ∪ δ. ⊃.(∃ γ,δ).γ⊂ α.δ⊂ β.ρ=γ∪δ.
[*22·72] ⊃.ρ⊂ α∪β.
[*60·2] ⊃.ρ∈Clʻ (α∪β) (4)
⊢.(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·45 -/
/- PM-VERBATIM-BEGIN PM1:✱60·5
✱60·5. ⊢ . sʻCl exʻα = α
Dem.
⊢.*40·1.*60·2.⊃⊢:x∈ sʻ Clʻ α. ≡.(∃ β).β⊂ α.x∈β. (1)
[*22·441] ⊃.x∈α (2)
⊢.*22·42. ⊃⊢:x∈α.⊃.α⊂ α.x∈α.
[*10·24] ⊃.(∃ β).β⊂ α.x∈β.
[(1)] ⊃.x∈ sʻ Clʻα (3)
⊢.(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·5 -/
/- PM-VERBATIM-BEGIN PM1:✱60·501
✱60·501. ⊢ . pʻClʻα = Λ
Dem.
⊢.*40·11.*60·21. ⊃⊢:x∈ sʻCl exʻ α.≡.(∃ β).β⊂ α.∃ !β.x∈β. (1)
[*22·441] ⊃.x∈α (2)
⊢.*22·42. ⊃⊢:x∈α.⊃.α⊂ α.x∈α.
[*10·24.*24·5.*4·7] ⊃.α⊂ α.∃ !α.x∈α.
[*10·24] ⊃.(∃ β).β⊂ α.∃ !β.x∈β.
[(1)] ⊃.x∈ sʻCl exʻα (3)
⊢.(2).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·501 -/
/- PM-VERBATIM-BEGIN PM1:✱60·51
✱60·51. ⊢ : sʻκ ⊂ β .≡. κ ⊂ Clʻβ
PM-VERBATIM-END PM1:✱60·51 -/
/- PM-VERBATIM-BEGIN PM1:✱60·52
✱60·52. ⊢ : β ⊂ pʻκ .≡. β ∈ pʻClʻʻκ
PM-VERBATIM-END PM1:✱60·52 -/
/- PM-VERBATIM-BEGIN PM1:✱60·53
✱60·53. ⊢ . Clʻpʻκ = pʻClʻʻκ
Dem.
⊢.*40·15.*60·2.⊃⊢:. β⊂ pʻ κ. ≡:γ∈κ.⊃_γ.β∈Clʻγ:
[*40·41.*60·14] ≡:β∈ pʻClʻʻ κ:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·53 -/
/- PM-VERBATIM-BEGIN PM1:✱60·54
✱60·54. ⊢ : Clʻα = Clʻβ .≡. α = β
PM-VERBATIM-END PM1:✱60·54 -/
/- PM-VERBATIM-BEGIN PM1:✱60·55
✱60·55. ⊢ : Cl exʻα = Cl exʻβ .≡. α = β
Dem.
⊢.*30·37.*60·14. ⊃⊢:α=β.⊃.Clʻ α=Clʻβ (1)
⊢.*30·37. ⊃⊢:Clʻ α=Clʻβ.⊃.sʻClʻ α=sʻClʻβ.
[*60·5] ⊃.α=β (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·55 -/
/- PM-VERBATIM-BEGIN PM1:✱60·56
✱60·56. ⊢ . κ ⊂ Clʻsʻκ
Proof as in *60·55
PM-VERBATIM-END PM1:✱60·56 -/
/- PM-VERBATIM-BEGIN PM1:✱60·57
✱60·57. ⊢ : x ∈ α .⊃. ιʻx ∈ Cl exʻα
Dem.
⊢.*40·13.*60·2. ⊃⊢:α∈κ.⊃.α∈Clʻ sʻ κ (1)
⊢.(1).*10·11.*22·1. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·57 -/
/- PM-VERBATIM-BEGIN PM1:✱60·6
✱60·6. ⊢ : x,y ∈ α .⊃. ιʻx ∪ ιʻy ∈ Cl exʻα
PM-VERBATIM-END PM1:✱60·6 -/
/- PM-VERBATIM-BEGIN PM1:✱60·61
✱60·61. ⊢ . Clʻα ∈ Cls²
PM-VERBATIM-END PM1:✱60·61 -/
/- PM-VERBATIM-BEGIN PM1:✱60·62
✱60·62. ⊢ . Cls² = ClʻCls
PM-VERBATIM-END PM1:✱60·62 -/
/- PM-VERBATIM-BEGIN PM1:✱60·7
✱60·7. ⊢ . Cls³ = ClʻCls²
Dem.
⊢.*60·2.⊃⊢:β∈Clʻ α. ≡.β⊂α.
[*22·1.*20·1·3] ≡.(∃ φ,ψ).α=ẑ(φ!z).β=ẑ(ψ!z).ψ!x⊃ₓφ!x.
[*10·5] ⊃.(∃ ψ).β=ẑ(ψ!z).
[*20·4] ⊃.β∈Cls (1)
⊢.(1).*60·2.(*60·03).⊃⊢.Prop
PM-VERBATIM-END PM1:✱60·7 -/

/- PM-VERBATIM-BEGIN PM1:✱60·71
✱60·71. ⊢.Cls²=ClʻCls [(*60·03)]
PM-VERBATIM-END PM1:✱60·71 -/
/- PM-VERBATIM-BEGIN PM1:✱60·72
✱60·72. ⊢.Cls³=ClʻCls² [(*60·04)]
PM-VERBATIM-END PM1:✱60·72 -/
