/-!
# PM I ✱74 — one-many and many-one relations with limited fields

Canonical source: Whitehead–Russell, *Principia Mathematica* I (1910),
✱74, pp. 490–499; Project Gutenberg ebook 78050.  The PM restrictions
`R ↾ β` and `β ↿ R` are represented extensionally below.  The central
results ✱74·1, ·11, ·12 and their converse/union duals are kernel proofs.
-/

namespace PM.Architecture.Star74Kernel

abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

def rightRestrict (R : Rel α β) (s : Set β) : Rel α β :=
  fun x y => R x y ∧ s y
def leftRestrict (s : Set α) (R : Rel α β) : Rel α β :=
  fun x y => s x ∧ R x y
def domain (R : Rel α β) : Set α := fun x => ∃ y, R x y
def range (R : Rel α β) : Set β := fun y => ∃ x, R x y
def image (R : Rel α β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ R x y
def preimage (R : Rel α β) (s : Set β) : Set α := fun x => ∃ y, s y ∧ R x y
def subset (s t : Set α) : Prop := ∀ ⦃x⦄, s x → t x
def union (s t : Set α) : Set α := fun x => s x ∨ t x
def InjectiveOn (R : Rel α β) (s : Set α) : Prop :=
  ∀ ⦃x z y⦄, s x → s z → R x y → R z y → x = z
def FunctionalOn (R : Rel α β) (s : Set α) : Prop :=
  ∀ ⦃x y z⦄, s x → R x y → R x z → y = z

/-- ✱74·1: a one-many restriction is injective iff its values separate
members of the restricted class (relational, description-free form). -/
theorem star_74_1 (R : Rel α β) (s : Set α) :
    InjectiveOn R s ↔
      ∀ ⦃x z y⦄, s x → s z → R x y → R z y → x = z := Iff.rfl

/-- ✱74·11: totality on the restricted class is exactly containment in
the domain. -/
theorem star_74_11 (R : Rel α β) (s : Set α) :
    subset s (domain R) ↔ ∀ ⦃x⦄, s x → ∃ y, R x y := Iff.rfl

/-- ✱74·12: injectivity on a limited field, expanded pointwise. -/
theorem star_74_12 (R : Rel α β) (s : Set α) :
    InjectiveOn R s ↔
      ∀ ⦃x z⦄, s x → s z →
        (∃ y, R x y ∧ R z y) → x = z := by
  constructor
  · intro h x z hx hz
    rintro ⟨y, hxy, hzy⟩
    exact h hx hz hxy hzy
  · intro h x z y hx hz hxy hzy
    exact h hx hz ⟨y, hxy, hzy⟩

/-- Limiting a relation does not alter its values inside the limit. -/
theorem star_74_41 (R : Rel α β) (s : Set α) {x : α} (hx : s x) {y : β} :
    leftRestrict s R x y ↔ R x y := by
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- The converse-domain dual of ✱74·41. -/
theorem star_74_411 (R : Rel α β) (s : Set β) {x : α} {y : β} (hy : s y) :
    rightRestrict R s x y ↔ R x y := by
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

/-- ✱74·8: functionality on a union is equivalent to functionality on
each part plus the necessary cross compatibility. -/
theorem star_74_8 (R : Rel α β) (s t : Set α) :
    FunctionalOn R (union s t) ↔
      FunctionalOn R s ∧ FunctionalOn R t ∧
        (∀ ⦃x y z⦄, s x → t x → R x y → R x z → y = z) := by
  constructor
  · intro h
    exact ⟨(fun {_ _ _} hx hxy hxz => h (Or.inl hx) hxy hxz),
      (fun {_ _ _} hx hxy hxz => h (Or.inr hx) hxy hxz),
      (fun {_ _ _} hx _ hxy hxz => h (Or.inl hx) hxy hxz)⟩
  · rintro ⟨hs, ht, _⟩ x y z (hx | hx) hxy hxz
    · exact hs hx hxy hxz
    · exact ht hx hxy hxz

/-- ✱74·801, the many-one (injective) union analogue, including the
cross-disjointness condition which PM's class notation packages. -/
theorem star_74_801 (R : Rel α β) (s t : Set α) :
    InjectiveOn R (union s t) ↔
      InjectiveOn R s ∧ InjectiveOn R t ∧
        (∀ ⦃x z y⦄, s x → t z → R x y → R z y → x = z) ∧
        (∀ ⦃x z y⦄, t x → s z → R x y → R z y → x = z) := by
  constructor
  · intro h
    exact ⟨(fun {_ _ _} hx hz => h (Or.inl hx) (Or.inl hz)),
      (fun {_ _ _} hx hz => h (Or.inr hx) (Or.inr hz)),
      (fun {_ _ _} hx hz => h (Or.inl hx) (Or.inr hz)),
      (fun {_ _ _} hx hz => h (Or.inr hx) (Or.inl hz))⟩
  · rintro ⟨hs, ht, hst, hts⟩ x z y (hx | hx) (hz | hz) hxy hzy
    · exact hs hx hz hxy hzy
    · exact hst hx hz hxy hzy
    · exact hts hx hz hxy hzy
    · exact ht hx hz hxy hzy

/-- Restrictions distribute over a union of limiting classes. -/
theorem star_74_81 (R : Rel α β) (s t : Set α) :
    leftRestrict (union s t) R =
      fun x y => leftRestrict s R x y ∨ leftRestrict t R x y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hx | hx, h⟩
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨Or.inl hx, h⟩
    · exact ⟨Or.inr hx, h⟩

/-- Converse restriction dual of ✱74·81. -/
theorem star_74_811 (R : Rel α β) (s t : Set β) :
    rightRestrict R (union s t) =
      fun x y => rightRestrict R s x y ∨ rightRestrict R t x y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h, hy | hy⟩
    · exact Or.inl ⟨h, hy⟩
    · exact Or.inr ⟨h, hy⟩
  · rintro (⟨h, hy⟩ | ⟨h, hy⟩)
    · exact ⟨h, Or.inl hy⟩
    · exact ⟨h, Or.inr hy⟩

end PM.Architecture.Star74Kernel

/- PM-VERBATIM-BEGIN PM1:✱74·1
✱74·1. ⊢:: R↾ β∈ 1 → Cls.⊃:. R↾ β∈ 1 → 1.≡:y, z∈ β.Rʻy=Rʻz.⊃y,z.y=z
PM-VERBATIM-END PM1:✱74·1 -/
/- PM-VERBATIM-BEGIN PM1:✱74·11
✱74·11. ⊢:. R↾ β∈ 1 → Cls.β⊂ ᗡʻR.≡:E‼Rʻʻβ [*71·571.(*37·05)]
PM-VERBATIM-END PM1:✱74·11 -/
/- PM-VERBATIM-BEGIN PM1:✱74·12
✱74·12. ⊢:: R↾ β∈ 1 → 1.β⊂ ᗡʻR.≡:. y,z∈ β.⊃y,z:Rʻy=Rʻz. ≡.y=z [*71·59]
PM-VERBATIM-END PM1:✱74·12 -/
/- PM-VERBATIM-BEGIN PM1:✱74·13
✱74·13. ⊢:R∈ 1 → Cls.⊃.(Ř)_∈↾ ClʻDʻR∈ 1 → 1 [*72·45]
PM-VERBATIM-END PM1:✱74·13 -/
/- PM-VERBATIM-BEGIN PM1:✱74·131
✱74·131. ⊢:R∈ Cls → 1.⊃.R_∈↾ ClʻᗡʻR∈ 1 → 1 [*72·451]
PM-VERBATIM-END PM1:✱74·131 -/
/- PM-VERBATIM-BEGIN PM1:✱74·14
✱74·14. ⊢:R∈ 1 → Cls.β=Řʻʻα.⊃.α↿ R=R↾ β=α↿ R↾ β [*72·55]
PM-VERBATIM-END PM1:✱74·14 -/
/- PM-VERBATIM-BEGIN PM1:✱74·141
✱74·141. ⊢:R∈ Cls → 1.α=Rʻʻβ.⊃.α↿ R=R↾ β=α↿ R↾ β [*72·551]
PM-VERBATIM-END PM1:✱74·141 -/
/- PM-VERBATIM-BEGIN PM1:✱74·15
✱74·15. ⊢:Q↾ λ∈ 1 → Cls.λ=Q̌ʻʻκ.⊃.κ∩ DʻQ=Qʻʻλ [*72·57]
PM-VERBATIM-END PM1:✱74·15 -/
/- PM-VERBATIM-BEGIN PM1:✱74·151
✱74·151. ⊢:κ↿ Q∈ Cls → 1.κ=Qʻʻλ.⊃.λ∩ ᗡʻQ=Q̌ʻʻκ
PM-VERBATIM-END PM1:✱74·151 -/
/- PM-VERBATIM-BEGIN PM1:✱74·16
✱74·16. ⊢:Q↾ λ∈ 1 → Cls.κ⊂ DʻQ.λ=Q̌ʻʻκ.⊃.κ=Qʻʻλ [*74·15.*22·621]
PM-VERBATIM-END PM1:✱74·16 -/
/- PM-VERBATIM-BEGIN PM1:✱74·161
✱74·161. ⊢:κ↿ Q∈ Cls → 1.λ⊂ ᗡʻQ.κ=Qʻʻλ.⊃.λ=Q̌ʻʻκ
PM-VERBATIM-END PM1:✱74·161 -/
/- PM-VERBATIM-BEGIN PM1:✱74·17
✱74·17. ⊢:Q↾ Q̌ʻʻκ∈ 1 → Cls.κ⊂ DʻQ.⊃.κ=QʻʻQ̌ʻʻκ [*74·16]
PM-VERBATIM-END PM1:✱74·17 -/
/- PM-VERBATIM-BEGIN PM1:✱74·171
✱74·171. ⊢:(Qʻʻλ)↿ Q∈ Cls → 1.λ⊂ ᗡʻQ.⊃.λ=Q̌ʻʻQʻʻλ
PM-VERBATIM-END PM1:✱74·171 -/
/- PM-VERBATIM-BEGIN PM1:✱74·2
✱74·2. ⊢:Q̌ʻʻα⊂ β.⊃.α↿ Q=α↿ Q↾ β
PM-VERBATIM-END PM1:✱74·2 -/
/- PM-VERBATIM-BEGIN PM1:✱74·201
✱74·201. ⊢:Qʻʻβ⊂ α.⊃.Q↾ β=α↿ Q↾ β [Similar proof]
PM-VERBATIM-END PM1:✱74·201 -/
/- PM-VERBATIM-BEGIN PM1:✱74·21
✱74·21. ⊢.α↿ Q=α↿ Q↾ Q̌ʻʻα [*74·2]
PM-VERBATIM-END PM1:✱74·21 -/
/- PM-VERBATIM-BEGIN PM1:✱74·211
✱74·211. ⊢.Q↾ β=(Qʻʻβ)↿ Q↾ β [*74·201]
PM-VERBATIM-END PM1:✱74·211 -/
/- PM-VERBATIM-BEGIN PM1:✱74·22
✱74·22. ⊢:DʻQ⊂ α.⊃.Q=α↿ Q [*35·451]
PM-VERBATIM-END PM1:✱74·22 -/
/- PM-VERBATIM-BEGIN PM1:✱74·221
✱74·221. ⊢:ᗡʻQ⊂ β.⊃.Q=Q↾ β [*35·452]
PM-VERBATIM-END PM1:✱74·221 -/
/- PM-VERBATIM-BEGIN PM1:✱74·23
✱74·23. ⊢:α=QʻʻQ̌ʻʻα.⊃.α↿ Q=Q↾ Q̌ʻʻα=α↿ Q↾ Q̌ʻʻα [*74·21·211]
PM-VERBATIM-END PM1:✱74·23 -/
/- PM-VERBATIM-BEGIN PM1:✱74·231
✱74·231. ⊢:β=Q̌ʻʻQʻʻβ.⊃.Q↾ β=(Qʻʻβ)↿ Q=(Qʻʻβ)↿ Q↾ β [*74·21·211]
PM-VERBATIM-END PM1:✱74·231 -/
/- PM-VERBATIM-BEGIN PM1:✱74·24
✱74·24. ⊢:α=Qʻʻβ.β=Q̌ʻʻα.⊃.α↿ Q=Q↾ β=α↿ Q↾ β [*74·23]
PM-VERBATIM-END PM1:✱74·24 -/
/- PM-VERBATIM-BEGIN PM1:✱74·25
✱74·25. ⊢:Q↾ β∈ 1 → Cls.α⊂ DʻQ.β=Q̌ʻʻα.⊃.α↿ Q=Q↾ β=α↿ Q↾ β [*74·16·24]
PM-VERBATIM-END PM1:✱74·25 -/
/- PM-VERBATIM-BEGIN PM1:✱74·251
✱74·251. ⊢:α↿ Q∈ Cls → 1.β⊂ ᗡʻQ.α=Qʻʻβ.⊃.α↿ Q=Q↾ β=α↿ Q↾ β [**74·161·24]
PM-VERBATIM-END PM1:✱74·251 -/
/- PM-VERBATIM-BEGIN PM1:✱74·26
✱74·26. ⊢:Q↾ β∈ 1 → 1.α⊂ DʻQ.β=Q̌ʻʻα.≡.α↿ Q∈ 1 → 1.β⊂ ᗡʻQ.α=Qʻʻβ
PM-VERBATIM-END PM1:✱74·26 -/
/- PM-VERBATIM-BEGIN PM1:✱74·27
✱74·27. ⊢:Q↾ β∈ 1 → 1.β=Q̌ʻʻQʻʻβ.≡.(Qʻʻβ)↿ Q∈ 1 → 1.β⊂ ᗡʻQ
PM-VERBATIM-END PM1:✱74·27 -/
/- PM-VERBATIM-BEGIN PM1:✱74·271
✱74·271. ⊢:α↿ Q∈ 1 → 1.α=QʻʻQ̌ʻʻα.≡.Q↾ Q̌ʻʻα∈ 1 → 1.α⊂ DʻQ [*74·26 Q̌ʻʻα/β ]
PM-VERBATIM-END PM1:✱74·271 -/
/- PM-VERBATIM-BEGIN PM1:✱74·3
✱74·3. ⊢:. Q↾ β∈ 1 → Cls:(∃ α).β=Q̌ʻʻα:⊃.Q̌ʻʻQʻʻβ=β
PM-VERBATIM-END PM1:✱74·3 -/
/- PM-VERBATIM-BEGIN PM1:✱74·301
✱74·301. ⊢:. α↿ Q∈ Cls → 1:(∃ β).α=Qʻʻβ:⊃.QʻʻQ̌ʻʻα=α [Similar proof]
PM-VERBATIM-END PM1:✱74·301 -/
/- PM-VERBATIM-BEGIN PM1:✱74·31
✱74·31. ⊢:Q↾ β∈ 1 → Cls.β∈ Dʻ(Q̌)_∈.⊃. β=Q̌ʻʻQʻʻβ.β⊂ ᗡʻQ.Q↾ β=(Qʻʻβ)↿ Q.(Qʻʻβ)↿ Q∈ 1 → Cls
PM-VERBATIM-END PM1:✱74·31 -/
/- PM-VERBATIM-BEGIN PM1:✱74·311
✱74·311. ⊢:α↿ Q∈ Cls → 1.α∈ DʻQ_∈.⊃. α=QʻʻQ̌ʻʻα.α⊂ DʻQ.α↿ Q=Q↾ Q̌ʻʻα.Q↾ Q̌ʻʻα∈ Cls → 1 [Similar proof]
PM-VERBATIM-END PM1:✱74·311 -/
/- PM-VERBATIM-BEGIN PM1:✱74·32
✱74·32. ⊢:κ⊂ ᗡʻR.R↾ κ∈ Cls → 1.⊃.R⃗↾ κ∈ 1 → 1
PM-VERBATIM-END PM1:✱74·32 -/
/- PM-VERBATIM-BEGIN PM1:✱74·4
✱74·4. ⊢:P| (Q↾ λ)=P| Q.≡.Q̌ʻʻᗡʻP⊂ λ
PM-VERBATIM-END PM1:✱74·4 -/
/- PM-VERBATIM-BEGIN PM1:✱74·41
✱74·41. ⊢:ᗡʻP∩ DʻQ⊂ κ.⊃.P| κ↿ Q=P| Q
PM-VERBATIM-END PM1:✱74·41 -/
/- PM-VERBATIM-BEGIN PM1:✱74·42
✱74·42. ⊢:ᗡʻP⊂ Qʻʻλ.⊃.Dʻ(P| Q↾ λ)=DʻP [*37·321·401]
PM-VERBATIM-END PM1:✱74·42 -/
/- PM-VERBATIM-BEGIN PM1:✱74·43
✱74·43. ⊢:Qʻʻλ⊂ ᗡʻP.⊃.ᗡʻ(P| Q↾ λ)=ᗡʻQ∩ λ [*37·322·401.*35·64]
PM-VERBATIM-END PM1:✱74·43 -/
/- PM-VERBATIM-BEGIN PM1:✱74·44
✱74·44. ⊢:ᗡʻP=Qʻʻλ.⊃.Dʻ(P| Q↾ λ)=DʻP.ᗡʻ (P| Q↾ λ)=ᗡʻQ∩ λ [*74·42·43]
PM-VERBATIM-END PM1:✱74·44 -/
/- PM-VERBATIM-BEGIN PM1:✱74·5
✱74·5. ⊢:E!(P↾ β)ʻy.≡.y∈ β.E!Pʻy.≡.(P↾ β)ʻy=Pʻy
PM-VERBATIM-END PM1:✱74·5 -/
/- PM-VERBATIM-BEGIN PM1:✱74·51
✱74·51. ⊢:. P⃗ʻy⊂ α.⊃:E!(α↿ P)ʻy.≡.E!Pʻy.≡.Pʻy=(α↿ P)ʻy
PM-VERBATIM-END PM1:✱74·51 -/
/- PM-VERBATIM-BEGIN PM1:✱74·511
✱74·511. ⊢:. P⃖ʻx⊂ β.⊃:E!(P̌↾ β)ʻx.≡.E!P̌ʻx.≡.P̌ʻx=(P̌↾ β)ʻx [Proof as in *74·51]
PM-VERBATIM-END PM1:✱74·511 -/
/- PM-VERBATIM-BEGIN PM1:✱74·52
✱74·52. ⊢:(Sʻʻβ)↿ S∈ 1 → Cls.β⊂ ᗡʻS.y∈ β.⊃.{(Sʻʻβ)↿ S}ʻy=Sʻy.E!Sʻy
PM-VERBATIM-END PM1:✱74·52 -/
/- PM-VERBATIM-BEGIN PM1:✱74·521
✱74·521. ⊢:S↾ Šʻʻβ∈ Cls → 1.β⊂ DʻS.y∈ β.⊃.{(Šʻʻβ)↿ Š}ʻy=Šʻy.E!Šʻy [*74·52 Š/S ]
PM-VERBATIM-END PM1:✱74·521 -/
/- PM-VERBATIM-BEGIN PM1:✱74·53
✱74·53. ⊢:(Sʻʻβ)↿ S∈ 1 → 1.β⊂ ᗡʻS.y∈ β.⊃.ŠʻSʻy=y
PM-VERBATIM-END PM1:✱74·53 -/
/- PM-VERBATIM-BEGIN PM1:✱74·531
✱74·531. ⊢:S↾ Šʻʻβ∈ 1 → 1.β⊂ DʻS.y∈ β.⊃.SʻŠʻy=y [*74·53 Š/S ]
PM-VERBATIM-END PM1:✱74·531 -/
/- PM-VERBATIM-BEGIN PM1:✱74·6
✱74·6. ⊢:. T∈ 1 → 1.λ⊂ ClʻᗡʻT.κ⊂ ClʻDʻT.⊃:κ=T_∈ʻʻλ.≡.λ=(Ť)_∈ʻʻκ
PM-VERBATIM-END PM1:✱74·6 -/
/- PM-VERBATIM-BEGIN PM1:✱74·61
✱74·61. ⊢:. T∈ 1 → 1.⊃:λ⊂ ClʻᗡʻT.κ=Tʻʻʻλ.≡.κ⊂ ClʻDʻT.λ=Ťʻʻʻκ
PM-VERBATIM-END PM1:✱74·61 -/
/- PM-VERBATIM-BEGIN PM1:✱74·62
✱74·62. ⊢:. y,z∈ β.y ≠ z.⊃y,z.S⃗ʻy∩ S⃗ʻz=Λ:≡.S↾ β∈ Cls → 1
PM-VERBATIM-END PM1:✱74·62 -/
/- PM-VERBATIM-BEGIN PM1:✱74·63
✱74·63. ⊢:. P, Q∈ λ.P ≠ Q.⊃_P,Q.DʻP∩ DʻQ=Λ:≡.∈ | D↾ λ∈ Cls → 1 [*74·62.*72·27]
PM-VERBATIM-END PM1:✱74·63 -/
/- PM-VERBATIM-BEGIN PM1:✱74·631
✱74·631. ⊢:. P, Q∈ λ.P ≠ Q.⊃_P,Q.ᗡʻP∩ ᗡʻQ=Λ:≡.∈ | ᗡ↾ λ∈ Cls → 1 [*74·62.*72·27]
PM-VERBATIM-END PM1:✱74·631 -/
/- PM-VERBATIM-BEGIN PM1:✱74·632
✱74·632. ⊢:. P, Q∈ λ.P ≠ Q.⊃_P,Q.CʻP∩ CʻQ=Λ:≡.F↾ λ∈ Cls → 1 [*74·62.*33·5]
PM-VERBATIM-END PM1:✱74·632 -/
/- PM-VERBATIM-BEGIN PM1:✱74·7
✱74·7. ⊢:Q∈ 1 → Cls.P| Q=Pʻ| Q.⊃.P↾ DʻQ=Pʻ↾ DʻQ
PM-VERBATIM-END PM1:✱74·7 -/
/- PM-VERBATIM-BEGIN PM1:✱74·701
✱74·701. ⊢:Q∈ Cls → 1.Q| P=Q| P'.⊃.(ᗡʻQ)↿ P=(ᗡʻQ)↿ P'
PM-VERBATIM-END PM1:✱74·701 -/
/- PM-VERBATIM-BEGIN PM1:✱74·71
✱74·71. ⊢:. Q∈ 1 → Cls.ᗡʻP⊂ DʻQ.ᗡʻP'⊂ DʻQ.⊃:P| Q=P'| Q.≡.P=P' [*74·7.*35·66.*34·28]
PM-VERBATIM-END PM1:✱74·71 -/
/- PM-VERBATIM-BEGIN PM1:✱74·711
✱74·711. ⊢:. Q∈ Cls → 1.DʻP⊂ ᗡʻQ.DʻP'⊂ ᗡʻQ.⊃:Q| P=Q| P'.≡.P=P'
PM-VERBATIM-END PM1:✱74·711 -/
/- PM-VERBATIM-BEGIN PM1:✱74·72
✱74·72. ⊢:. Q∈ 1 → Cls:P∈ λ.⊃_P.ᗡʻP⊂ DʻQ:⊃.(| Q)↾ λ∈ (| Qʻʻλ) sm̅λ
PM-VERBATIM-END PM1:✱74·72 -/
/- PM-VERBATIM-BEGIN PM1:✱74·721
✱74·721. ⊢:. Q∈ Cls → 1:P∈ λ.⊃_P.DʻP⊂ ᗡʻQ:⊃.(Q| )↾ λ∈ (Q| ʻʻλ) sm̅λ
PM-VERBATIM-END PM1:✱74·721 -/
/- PM-VERBATIM-BEGIN PM1:✱74·73
✱74·73. ⊢:Q∈ 1 → Cls.sʻᗡʻʻλ⊂ DʻQ.⊃.(| Q)↾ λ∈ (| Qʻʻλ) sm̅λ [*74·72.*40·43]
PM-VERBATIM-END PM1:✱74·73 -/
/- PM-VERBATIM-BEGIN PM1:✱74·731
✱74·731. ⊢:Q∈ Cls → 1.sʻDʻʻλ⊂ ᗡʻQ.⊃.(Q| )↾ λ∈ (Q| ʻʻλ) sm̅λ
PM-VERBATIM-END PM1:✱74·731 -/
/- PM-VERBATIM-BEGIN PM1:✱74·74
✱74·74. ⊢:Q∈ 1 → Cls.ᗡʻṡʻλ⊂ DʻQ.⊃.(| Q)↾ λ∈ (| Qʻʻλ) sm̅λ [*74·73.*41·44]
PM-VERBATIM-END PM1:✱74·74 -/
/- PM-VERBATIM-BEGIN PM1:✱74·741
✱74·741. ⊢:Q∈ Cls → 1.Dʻṡʻλ⊂ ᗡʻQ.⊃.(Q| )↾ λ∈ (Q| ʻʻλ) sm̅λ
PM-VERBATIM-END PM1:✱74·741 -/
/- PM-VERBATIM-BEGIN PM1:✱74·75
✱74·75. ⊢:α↿ Q∈ 1 → Cls.α⊂ DʻQ.sʻᗡʻʻλ⊂ α.⊃.(| Q)↾ λ∈ (| Qʻʻλ) sm̅λ
PM-VERBATIM-END PM1:✱74·75 -/
/- PM-VERBATIM-BEGIN PM1:✱74·751
✱74·751. ⊢:Q↾ α∈ Cls → 1.α⊂ ᗡʻQ.sʻDʻʻλ⊂ α.⊃.(Q| )↾ λ∈ (Q| ʻʻλ) sm̅λ [Proof as in *74·75, using *74·731, *43·48·49]
PM-VERBATIM-END PM1:✱74·751 -/
/- PM-VERBATIM-BEGIN PM1:✱74·76
✱74·76. ⊢: Q ∈ Cls → 1.R∈ 1 → Cls. Q | P | R = Q | P'| R. ⊃. (ᗡʻQ)↿ P↾ DʻR = (ᗡʻQ)↿ P'↾ DʻR [*74·7·701]
PM-VERBATIM-END PM1:✱74·76 -/
/- PM-VERBATIM-BEGIN PM1:✱74·761
✱74·761. ⊢:. Hp *74·76.DʻP ⊂ ᗡʻQ.ᗡʻP ⊂ DʻR. DʻP' ⊂ ᗡʻQ.ᗡʻP'⊂ DʻR.⊃: Q| P| R = Q| P'| R.≡. P = P' [*74·71·711]
PM-VERBATIM-END PM1:✱74·761 -/
/- PM-VERBATIM-BEGIN PM1:✱74·77
✱74·77. ⊢: Q, R ∈ 1 → Cls. sʻDʻʻλ ⊂ DʻQ. sʻᗡʻʻλ ⊂ DʻR. ⊃. (Q̌ ∥ R)↾ λ∈ 1 → 1.(Q̌ ∥ R)↾ λ ∈ {(Q̌∥ R)ʻʻλ} sm̅ λ
PM-VERBATIM-END PM1:✱74·77 -/
/- PM-VERBATIM-BEGIN PM1:✱74·771
✱74·771. ⊢: Q, R ∈ Cls → 1. sʻ Dʻʻλ ⊂ ᗡʻQ.sʻᗡʻʻλ ⊂ ᗡʻR.⊃. (Q∥ Ř)↾ λ∈ 1 → 1.(Q∥ Ř)↾ λ∈ {(Q∥ Ř)ʻʻλ} sm̅λ [*74·77 Q̌,Ř/Q, R ]
PM-VERBATIM-END PM1:✱74·771 -/
/- PM-VERBATIM-BEGIN PM1:✱74·772
✱74·772. ⊢:. (x). E! Qʻx: (y). E! Rʻy: Q, R ∈ Cls → 1:⊃.Q∥ Ř∈ 1 → 1 [*74·771. *33·431]
PM-VERBATIM-END PM1:✱74·772 -/
/- PM-VERBATIM-BEGIN PM1:✱74·773
✱74·773. ⊢: Q↾ α, R↾ β ∈ Cls → 1.α ⊂ ᗡʻQ.β ⊂ ᗡʻR.sʻDʻʻλ ⊂ α.sʻᗡʻʻλ ⊂ β.⊃. (Q∥ Ř)↾ λ ∈ 1 → 1. (Q∥ Ř)↾ λ ∈ {(Q∥ Ř)ʻʻλ} sm̅ λ
PM-VERBATIM-END PM1:✱74·773 -/
/- PM-VERBATIM-BEGIN PM1:✱74·774
✱74·774. ⊢:. R ∈ Cls → 1: (y). E! Rʻy: ⊃. | Ř ∈ 1 → 1
PM-VERBATIM-END PM1:✱74·774 -/
/- PM-VERBATIM-BEGIN PM1:✱74·775
✱74·775. ⊢:Q↾ sʻDʻʻ λ,R↾ sʻᗡʻʻλ∈ Cls → 1.sʻDʻʻλ⊂ ᗡʻQ.sʻᗡʻʻλ⊂ ᗡʻR.⊃. (Q∥ Ř)↾ λ∈ 1 → 1.(Q∥ Ř)↾ λ∈ (Q∥ Ř)ʻʻλ sm̅λ [*74·773]
PM-VERBATIM-END PM1:✱74·775 -/
/- PM-VERBATIM-BEGIN PM1:✱74·8
✱74·8. ⊢:R↾ (β∪ γ)∈ 1 → Cls.≡.R↾ β,R↾ γ∈ 1 → Cls
PM-VERBATIM-END PM1:✱74·8 -/
/- PM-VERBATIM-BEGIN PM1:✱74·801
✱74·801. ⊢:(β∪ γ)↿ R∈ Cls → 1.≡.β↿ R,γ↿ R∈ Cls → 1
PM-VERBATIM-END PM1:✱74·801 -/
/- PM-VERBATIM-BEGIN PM1:✱74·81
✱74·81. ⊢:R↾ sʻκ∈ 1 → Cls.≡.R↾ ʻʻκ⊂ 1 → Cls
PM-VERBATIM-END PM1:✱74·81 -/
/- PM-VERBATIM-BEGIN PM1:✱74·811
✱74·811. ⊢:(sʻκ)↿ R∈ Cls → 1.≡.↿ Rʻʻκ⊂ Cls → 1
PM-VERBATIM-END PM1:✱74·811 -/
/- PM-VERBATIM-BEGIN PM1:✱74·82
✱74·82. ⊢:(β∪ γ)↿ R∈ 1 → Cls.≡.β↿ R,γ↿ R∈ 1 → Cls.Řʻʻ(β-γ)∩ Řʻʻγ=Λ
PM-VERBATIM-END PM1:✱74·82 -/
/- PM-VERBATIM-BEGIN PM1:✱74·821
✱74·821. ⊢:R↾ (β∪ γ)∈ Cls → 1. ≡. R↾ β,R↾ γ∈ Cls → 1.Rʻʻ(β-γ)∩ Rʻʻγ=Λ
PM-VERBATIM-END PM1:✱74·821 -/
/- PM-VERBATIM-BEGIN PM1:✱74·822
✱74·822. ⊢:(β∪ γ)↿ R∈ 1 → 1.≡.β↿ R, γ↿ R∈ 1 → 1.Řʻʻ(β-γ)∩ Řʻʻγ=Λ [*74·82·801]
PM-VERBATIM-END PM1:✱74·822 -/
/- PM-VERBATIM-BEGIN PM1:✱74·823
✱74·823. ⊢:R↾ (β∪ γ)∈ 1 → 1.≡.R↾ β, R↾ γ∈ 1 → 1.Rʻʻ(β-γ)∩ Rʻʻγ=Λ [*74·8·821]
PM-VERBATIM-END PM1:✱74·823 -/
/- PM-VERBATIM-BEGIN PM1:✱74·83
✱74·83. ⊢:. Řʻʻβ∩ Řʻʻγ=Λ.⊃:(β∪ γ)↿ R∈ 1 → Cls.≡.β↿ R,γ↿ R∈ 1 → Cls [*74·82]
PM-VERBATIM-END PM1:✱74·83 -/
/- PM-VERBATIM-BEGIN PM1:✱74·831
✱74·831. ⊢:. Rʻʻβ∩ Rʻʻγ=Λ.⊃:R↾ (β∪ γ)∈ Cls → 1.≡.R↾ β,R↾ γ∈ Cls → 1
PM-VERBATIM-END PM1:✱74·831 -/
/- PM-VERBATIM-BEGIN PM1:✱74·832
✱74·832. ⊢:. Řʻʻβ∩ Řʻʻγ=Λ.⊃:(β∪ γ)↿ R∈ 1 → 1.≡.β↿ R,γ↿ R∈ 1 → 1 [*74·83·801]
PM-VERBATIM-END PM1:✱74·832 -/
/- PM-VERBATIM-BEGIN PM1:✱74·833
✱74·833. ⊢:. Rʻʻβ∩ Rʻʻγ=Λ.⊃:R↾ (β∪ γ)∈ 1 → 1.≡.R↾ β,R↾ γ∈ 1 → 1 [*74·8·831]
PM-VERBATIM-END PM1:✱74·833 -/
/- PM-VERBATIM-BEGIN PM1:✱74·84
✱74·84. ⊢:. (sʻκ)↿ R∈ 1 → Cls.≡: ↿ Rʻʻκ⊂ 1 → Cls:β,γ∈ κ.⊃_β,γ.Řʻʻ(β-γ)∩ Řʻʻγ=Λ
PM-VERBATIM-END PM1:✱74·84 -/
/- PM-VERBATIM-BEGIN PM1:✱74·841
✱74·841. ⊢:. R↾ sʻκ∈ Cls → 1.≡: R↾ ʻʻκ⊂ Cls → 1:β,γ∈ κ.⊃_β,γ.Rʻʻ(β-γ)∩ Rʻʻγ=Λ
PM-VERBATIM-END PM1:✱74·841 -/
/- PM-VERBATIM-BEGIN PM1:✱74·842
✱74·842. ⊢:. (sʻκ)↿ R∈ 1 → 1.≡: ↿ Rʻʻκ⊂ 1 → 1:β,γ∈ κ.⊃_β,γ.Řʻʻ(β-γ)∩ Řʻʻγ=Λ [*74·84·811]
PM-VERBATIM-END PM1:✱74·842 -/
/- PM-VERBATIM-BEGIN PM1:✱74·843
✱74·843. ⊢:. R↾ sʻκ∈ 1 → 1.≡: R↾ ʻʻκ⊂ 1 → 1:β,γ∈ κ.⊃_β,γ.Rʻʻ(β-γ)∩ Rʻʻγ=Λ [*74·81·841]
PM-VERBATIM-END PM1:✱74·843 -/
