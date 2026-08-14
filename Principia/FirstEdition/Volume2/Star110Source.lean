/-! # Principia Mathematica II, ✱110 — arithmetical sums -/
/- PM-VERBATIM-BEGIN PM2:✱110·1
✱110·1. ⊢ . R∈α+β . ≡ : (∃σ) . x∈α . R=(ι‘x)↑[(Λ∩β)↑ι‘σ] : ∨ : (∃σ) . y∈β . R=(Λ∩α)↑[(ι‘y)↑ι‘σ]
PM-VERBATIM-END PM2:✱110·1 -/
/- PM-VERBATIM-BEGIN PM2:✱110·101
✱110·101. ⊢ . (ι‘x)↑(Λ∩β) disjoint (Λ∩α)↑(ι‘y)
PM-VERBATIM-END PM2:✱110·101 -/
/- PM-VERBATIM-BEGIN PM2:✱110·11
✱110·11. ⊢ . ι↑(Λ∩β)“ι“α ∩ (Λ∩α)↑“ι“β = Λ
PM-VERBATIM-END PM2:✱110·11 -/
/- PM-VERBATIM-BEGIN PM2:✱110·12
✱110·12. ⊢ . ι↑(Λ∩β)“ι“α sm α . (Λ∩α)↑“ι“β sm β
PM-VERBATIM-END PM2:✱110·12 -/
/- PM-VERBATIM-BEGIN PM2:✱110·13
✱110·13. ⊢ : γ sm α . δ sm β . γ∩δ=Λ . ⊃ . γ∪δ sm (α+β)
PM-VERBATIM-END PM2:✱110·13 -/
/- PM-VERBATIM-BEGIN PM2:✱110·14
✱110·14. ⊢ : α∩β=Λ . ⊃ . α∪β sm (α+β) [✱110·13 . ✱73·3]
PM-VERBATIM-END PM2:✱110·14 -/
/- PM-VERBATIM-BEGIN PM2:✱110·15
✱110·15. ⊢ : γ sm α . δ sm β . ⊃ . γ+δ sm α+β
PM-VERBATIM-END PM2:✱110·15 -/
/- PM-VERBATIM-BEGIN PM2:✱110·151
✱110·151. ⊢ : α∩β=Λ . ⊃ : ξ sm (α∪β) . ≡ . (∃γ,δ) . γ sm α . δ sm β . γ∩δ=Λ . ξ=γ∪δ
PM-VERBATIM-END PM2:✱110·151 -/
/- PM-VERBATIM-BEGIN PM2:✱110·152
✱110·152. ⊢ : ξ sm (α+β) . ≡ . (∃γ,δ) . γ sm α . δ sm β . γ∩δ=Λ . ξ=γ∪δ
PM-VERBATIM-END PM2:✱110·152 -/
/- PM-VERBATIM-BEGIN PM2:✱110·16
✱110·16. ⊢ . Nc‘(α+β) = ξ̂{(∃γ,δ) . γ sm α . δ sm β . γ∩δ=Λ . ξ=γ∪δ} [✱110·152 . ✱100·1]
PM-VERBATIM-END PM2:✱110·16 -/
/- PM-VERBATIM-BEGIN PM2:✱110·17
✱110·17. ⊢ : α∈tϵβ . ⊃ . ∃!Nc(t‘α)‘(α+β)
PM-VERBATIM-END PM2:✱110·17 -/
/- PM-VERBATIM-BEGIN PM2:✱110·18
✱110·18. ⊢ . α+β∈t³‘(t‘αⁿt‘β)
PM-VERBATIM-END PM2:✱110·18 -/
/- PM-VERBATIM-BEGIN PM2:✱110·2
✱110·2. ⊢ : ξ∈μ+ₜv . ≡ . (∃α,β) . μ=N₀c‘α . v=N₀c‘β . ξ sm (α+β) [✱110·02]
PM-VERBATIM-END PM2:✱110·2 -/
/- PM-VERBATIM-BEGIN PM2:✱110·201
✱110·201. ⊢ : ξ∈μ+ₜv . ≡ : μ,v∈NC : (∃α,β) . α∈μ . β∈v . ξ sm (α+β) [✱103·27 . ✱110·2]
PM-VERBATIM-END PM2:✱110·201 -/
/- PM-VERBATIM-BEGIN PM2:✱110·202
✱110·202. ⊢ : ξ∈μ+ₜv . ≡ : ∃!μ . ∃!v : (∃γ,δ) . μ=Nc‘γ . v=Nc‘δ . γ∩δ=Λ . ξ=γ∪δ
PM-VERBATIM-END PM2:✱110·202 -/
/- PM-VERBATIM-BEGIN PM2:✱110·21
✱110·21. ⊢ : μ,v∈NC . ⊃ : ξ∈μ+ₜv . ≡ . (∃α,β) . α∈μ . β∈v . ξ sm (α+β) [✱110·201]
PM-VERBATIM-END PM2:✱110·21 -/
/- PM-VERBATIM-BEGIN PM2:✱110·211
✱110·211. ⊢ : μ,v∈NC . ⊃ : ξ∈μ+ₜv . ≡ . (∃γ,δ) . γ∈sm“μ . δ∈sm“v . γ∩δ=Λ . ξ=γ∪δ
PM-VERBATIM-END PM2:✱110·211 -/
/- PM-VERBATIM-BEGIN PM2:✱110·212
✱110·212. ⊢ : μ,v∈NC . ⊃ : ξ∈μ+ₜv . ≡ . (∃γ) . γ∈sm“μ . γ⊂ξ . ξ−γ∈sm“v
PM-VERBATIM-END PM2:✱110·212 -/
/- PM-VERBATIM-BEGIN PM2:✱110·22
✱110·22. ⊢ . N₀c‘α+ₜN₀c‘β = Nc‘(α+β)
PM-VERBATIM-END PM2:✱110·22 -/
/- PM-VERBATIM-BEGIN PM2:✱110·221
✱110·221. ⊢ : ξ∈Nc(η)‘α+ₜNc(ζ)‘β . ≡ . ∃!Nc(η)‘α . ∃!Nc(ζ)‘β . ξ∈Nc‘(α+β)
PM-VERBATIM-END PM2:✱110·221 -/
namespace PM.FirstEdition.Volume2.Star110Source

abbrev Set' (α : Type u) := α → Prop

structure Bijection (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/-- ✱110·01. The disjoint (arithmetical) sum of two classes. -/
def SumClass (s : Set' α) (t : Set' β) : Set' (Sum α β)
  | .inl x => s x
  | .inr y => t y

/-- ✱110·02. Cardinal equivalence of classes. -/
def Equip (s : Set' α) (t : Set' β) : Prop :=
  Nonempty (Bijection {x // s x} {y // t y})

/-- ✱110·03. The cardinal represented by a class. -/
def Cardinal (s : Set' α) : (Type u) → Prop := fun γ => Nonempty (Bijection {x // s x} γ)

/-- ✱110·04. Cardinal addition, represented by disjoint sum. -/
def CardinalAdd (s : Set' α) (t : Set' β) := Cardinal (SumClass s t)

end PM.FirstEdition.Volume2.Star110Source
