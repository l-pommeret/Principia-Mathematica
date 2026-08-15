/-! PM II ✱120 opening. Gutenberg 78255, pp. 336–338. -/
/- PM-VERBATIM-BEGIN PM2:✱120·214
✱120·214. ⊢ : ρ sm σ .⊃: ρ∈Cls induct .≡. σ∈Cls induct
PM-VERBATIM-END PM2:✱120·214 -/
/- PM-VERBATIM-BEGIN PM2:✱120·26
✱120·26. ⊢ : ρ∈Cls induct : φη .⊃η,x. φ(η∪ιʻx) : φΛ :⊃. φρ
PM-VERBATIM-END PM2:✱120·26 -/
/- PM-VERBATIM-BEGIN PM2:✱120·311
✱120·311. ⊢ : ∃!α+₍c₎1 . α+₍c₎1=β+₍c₎1 .⊃. α=smʻʻβ . ∃!α
PM-VERBATIM-END PM2:✱120·311 -/
/- PM-VERBATIM-BEGIN PM2:✱120·152
✱120·152. ⊢ : α∈NC . smʻʻα∈NC induct−ιʻΛ .⊃. α∈NC induct−ιʻΛ
Dem.
⊢ .✱100·521. ⊃ ⊢ :Hp. ⊃ . sm ʻʻ sm ʻʻα =α .
[✱120·15] ⊃ .α ∈ NC induct (1)
⊢ .✱37·29. ⊃ ⊢ :Hp.⊃ .∃ !α (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·152 -/
/- PM-VERBATIM-BEGIN PM2:✱120·211
✱120·211. ⊢ : Ncʻρ∈NC induct−ιʻΛ .⊃. ρ∈Cls induct
Dem.
⊢ .✱100·511. ⊃ ⊢ :Hp.⊃. sm ʻʻNcʻp=N₀cʻρ .
[✱120·15] ⊃ . N₀cʻρ ∈ NC induct.
[✱120·21] ⊃ .ρ ∈ Cls induct:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·211 -/
/- PM-VERBATIM-BEGIN PM2:✱120·11
✱120·11. ⊢ : α∈NηC induct : φξ .⊃ξ. φ(ξ+₍c₎1) : φ0η :⊃. φα
PM-VERBATIM-END PM2:✱120·11 -/
/- PM-VERBATIM-BEGIN PM2:✱120·12
✱120·12. ⊢ . 0∈NC induct
PM-VERBATIM-END PM2:✱120·12 -/
/- PM-VERBATIM-BEGIN PM2:✱120·121
✱120·121. ⊢ : α∈NξC induct .⊃. (α+₍c₎1)ξ∈NξC induct
PM-VERBATIM-END PM2:✱120·121 -/
/- PM-VERBATIM-BEGIN PM2:✱120·13
✱120·13. ⊢ : α∈NηC induct : ξ∈NηC induct . φξ .⊃ξ. φ(ξ+₍c₎1) : φ0η :⊃. φα
Dem.
⊢ .✱120·121. ⊃ ⊢ :. ξ ∈ N_η C induct.φ ξ .⊃ _ξ .φ (ξ +c1):⊃ :
ξ ∈ N_η C induct.φ ξ .⊃ _ξ .(ξ +c1)_η ∈ N_η C induct.φ (ξ +c1) (1)
⊢ .✱120·12. ⊃ ⊢ :φ 0_η .⊃ .0_η ∈ N_η C induct.φ 0_η (2)
⊢ .(1).(2). ⊃ ⊢ :. Hp.⊃ :
ξ ∈ N_η C induct.φ ξ . ⊃ _ξ .(ξ +c1)_η ∈ N_η C induct.φ (ξ +c1):0_η ∈ N_η C induct.φ 0_η :
[✱120·11 ξ ∈ N_η C induct.φ ξ/φ ξ ] ⊃ :α ∈ N_η C induct.φ α :. ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·13 -/
/- PM-VERBATIM-BEGIN PM2:✱120·151
✱120·151. ⊢ : α∈NC induct . ∃!α .⊃. α+₍c₎1∈NC induct
Dem.
⊢ .✱120·15. ⊃ ⊢ :α ∈ N_ξ C induct.∃ !α . ⊃ . sm _η ʻʻα ∈ N_η C induct.
[✱120·121] ⊃ .( sm _η ʻʻα +c1)_η ∈ N_η C induct.
[✱118·241.✱120·14] ⊃ .(α +c1)_η ∈ N_η C induct:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·151 -/
/- PM-VERBATIM-BEGIN PM2:✱120·21
✱120·21. ⊢ : ρ∈Cls induct .≡. N₀cʻρ∈NC induct
Dem.
⊢ .✱120·14·2. ⊃ ⊢ :ρ ∈ Cls induct. ≡ .(∃ α ).α ∈ NC induct.α ∈ NC.ρ ∈ α .
[✱103·27] ≡ .(∃ α ).α ∈ NC induct. N₀cʻρ =α .
[✱13·195] ≡ .N₀cʻρ ∈ NC induct:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·21 -/
/- PM-VERBATIM-BEGIN PM2:✱120·212
✱120·212. ⊢ . Λ∈Cls induct [✱120·211·12]
PM-VERBATIM-END PM2:✱120·212 -/
/- PM-VERBATIM-BEGIN PM2:✱120·15
✱120·15. ⊢ : α∈NC induct . ∃!α .⊃. smʻʻα∈NC induct
Dem.
⊢ .✱101·15.✱120·12. ⊃ ⊢ . sm _η ʻʻ0_ξ ∈ N_η C induct (1)
⊢ .✱110·4. ⊃ ⊢ .α =Λ _ξ .⊃ .(α +c1)_ξ = Λ _ξ (2)
⊢ .✱118·201. ⊃ ⊢ :∃ !(α +c1)_ξ .⊃ . sm _η ʻʻ(α +c1)_ξ =(α +c1)_η
[✱118·241.✱110·4] = ( sm _η ʻʻα +c 1)_η (3)
⊢ .✱120·121. ⊃ ⊢ :∃ !(α +c1)_ξ . sm _η ʻʻα ∈ N_η C induct.⊃ .( sm _η ʻʻα +c1)_η ∈ N_η C induct.
[(3)] ⊃ . sm _η ʻʻ(α +c1)_ξ ∈ 1 N_Cinduct (4)
⊢ .(4).✱2·2. ⊃ ⊢ :. sm _η ʻʻα ∈ N_η C induct.⊃ :
(α +c1)_ξ =Λ _ξ .∨. sm _η ʻʻ(α +c1)_ξ ∈ N_η C induct (5)
⊢ .(2).(5).✱3·48. ⊃ ⊢ :. α =Λ _ξ .∨. sm _η ʻʻα ∈ N_η C induct:⊃ :
(α +c1)_ξ =Λ _ξ .∨. sm _η ʻʻ(α +c1)_ξ ∈ N_η C induct (6)
⊢ .(1).(6).✱120·11.✱4·6.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱120·15 -/
/- PM-VERBATIM-BEGIN PM2:✱120·213
✱120·213. ⊢ . ιʻα∈Cls induct  [✱120·211·122]
PM-VERBATIM-END PM2:✱120·213 -/
/- PM-VERBATIM-BEGIN PM2:✱120·251
✱120·251. ⊢ : η∈Cls induct .⊃. η∪ιʻy∈Cls induct
PM-VERBATIM-END PM2:✱120·251 -/
