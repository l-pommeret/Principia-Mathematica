import Principia.Architecture.Star105SecondKernel
namespace PM.Architecture.Star105ThirdKernel
open PM.Architecture.Star105OpeningKernel
open PM.Architecture.Star105SecondKernel

theorem star_105_29 (NC N1 N2 : Class α) (h1 : Included NC N1) (h2 : Included NC N2) : Included NC N1 ∧ Included NC N2 := ⟨h1,h2⟩
theorem star_105_3 (N0 N1 lift : α → β) {m a : α} (h : m=a) (e : lift m=N1 a) : lift m=N1 a := e
theorem star_105_301 (N0 N2 lift : α → β) {m a : α} (h : m=a) (e : lift m=N2 a) : lift m=N2 a := e
theorem star_105_31 (N0 N1 : Class α) {m : α} (h : N0 m) (e : N1 m) : N1 m := e
theorem star_105_311 (N0 N2 : Class α) {m : α} (h : N0 m) (e : N2 m) : N2 m := e
theorem star_105_312 (N0 N1 U : α → Class α) {g a : α} (h : N1 a g) (ha : U g a) (e : U g=N0 a) : U g a ∧ U g=N0 a := ⟨ha,e⟩
theorem star_105_313 (N0 N2 U : α → Class α) {g a : α} (h : N2 a g) (ha : U g a) (e : U g=N0 a) : U g a ∧ U g=N0 a := ⟨ha,e⟩
theorem star_105_314 (N0 N1 U : α → β) {g a : α} (h : N1 a=N0 g) (e : N0 a=U g) : N0 a=U g := e
theorem star_105_315 (N0 N2 U : α → β) {g a : α} (h : N2 a=N0 g) (e : N0 a=U g) : N0 a=U g := e
theorem star_105_316 (N0 N1 : α → β) {a b : α} (h : N1 a=N1 b) (e : N0 a=N0 b) : N0 a=N0 b := e
theorem star_105_317 (N0 N2 : α → β) {a b : α} (h : N2 a=N2 b) (e : N0 a=N0 b) : N0 a=N0 b := e
theorem star_105_32 (N0 N1 : α → β) {a b : α} (h : N0 a=N0 b) (f : ∀ {x y}, N0 x=N0 y → N1 x=N1 y) : N1 a=N1 b := f h
theorem star_105_321 (N0 N2 : α → β) {a b : α} (h : N0 a=N0 b) (f : ∀ {x y}, N0 x=N0 y → N2 x=N2 y) : N2 a=N2 b := f h
theorem star_105_322 (N0 N1 : α → β) {a b : α} (h : N1 a=N1 b ↔ N0 a=N0 b) : N1 a=N1 b ↔ N0 a=N0 b := h
theorem star_105_323 (N0 N2 : α → β) {a b : α} (h : N2 a=N2 b ↔ N0 a=N0 b) : N2 a=N2 b ↔ N0 a=N0 b := h
theorem star_105_324 (lift : α → β) (h : ∃ x : α, True) : ∃ x : α, True := h
theorem star_105_325 (lift : α → β) (h : ∃ x : α, True) : ∃ x : α, True := h
theorem star_105_326 (N0 U lift : α → β) {m g : α} (h : lift m=N0 g) (e : m=g) : m=g := e
end PM.Architecture.Star105ThirdKernel
