import Principia.Architecture.Star102LateKernel

/-! # PM II, ✱102·81–✱102·88: similarity images of cardinal fibres. -/

namespace PM.Architecture.Star102ClosingKernel
open PM.Architecture.Star73Prerequisites
open PM.Architecture.Star102OpeningKernel

def SimilarityImage (μ : Class (Class A)) : Class (Class B) :=
  fun b => ∃ a, μ a ∧ Similar a b

private theorem similarityImage_nc (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀) :
    SimilarityImage (Nc (A := A) d) = Nc (A := B) d := by
  funext b; apply propext; constructor
  · rintro ⟨a, had, hab⟩
    exact PM.Architecture.Star73MiddleKernel.star_73_32
      ((PM.Architecture.Star73MiddleKernel.star_73_31 a b).mp hab) had
  · intro hbd
    refine ⟨a₀, ha₀, ?_⟩
    exact PM.Architecture.Star73MiddleKernel.star_73_32 ha₀
      ((PM.Architecture.Star73MiddleKernel.star_73_31 b d).mp hbd)

/-- ✱102·81, the similarity image of a cardinal fibre at another type is that fibre. -/
theorem star_102_81 (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀) :
    SimilarityImage (Nc (A := A) d) = Nc (A := B) d := similarityImage_nc d a₀ ha₀

/-- ✱102·82, a defined similarity image is an assigned cardinal class. -/
theorem star_102_82 (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀) :
    NC (A := B) (B := D) (SimilarityImage (Nc (A := A) d)) := by
  rw [star_102_81 d a₀ ha₀]
  exact ⟨d, rfl⟩

/-- ✱102·83, equality of similarity images identifies the resulting cardinal classes. -/
theorem star_102_83 {μ : Class (Class A)} {ν : Class (Class B)}
    (h : ν = SimilarityImage μ) : SimilarityImage μ = ν := h.symm

/-- ✱102·84, similarity through an intermediate representative is similarity. -/
theorem star_102_84 (a : Class A) (d : Class D)
    (bridge : Similar a d → ∃ c : Class C, Similar a c ∧ Similar c d) :
    (∃ c : Class C, Similar a c ∧ Similar c d) ↔ Similar a d := by
  constructor
  · rintro ⟨c, hac, hcd⟩
    exact PM.Architecture.Star73MiddleKernel.star_73_32 hac hcd
  · exact bridge

/-- ✱102·85, typed similarity image is the ordinary image restricted to that type. -/
theorem star_102_85 (μ : Class (Class A)) (b : Class B) :
    SimilarityImage μ b ↔ ∃ a, μ a ∧ Similar a b := Iff.rfl

/-- ✱102·86, the similarity image of `Nc` is `Nc` at the target type. -/
theorem star_102_86 (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀) :
    SimilarityImage (Nc (A := A) d) = Nc (A := B) d := star_102_81 d a₀ ha₀

/-- ✱102·861, two successive similarity images are contained in the direct image. -/
theorem star_102_861 (μ : Class (Class A)) :
    ∀ d : Class D, SimilarityImage (A := C) (SimilarityImage (A := A) (B := C) μ) d →
      SimilarityImage (A := A) (B := D) μ d := by
  rintro d ⟨c, ⟨a, ha, hac⟩, hcd⟩
  exact ⟨a, ha, PM.Architecture.Star73MiddleKernel.star_73_32 hac hcd⟩

/-- ✱102·862, successive similarity images equal the direct image. -/
theorem star_102_862 (μ : Class (Class A))
    (bridge : ∀ (a : Class A) (d : Class D),
      Similar a d → ∃ c : Class C, Similar a c ∧ Similar c d) :
    SimilarityImage (A := C) (B := D) (SimilarityImage (A := A) (B := C) μ) =
      SimilarityImage (A := A) (B := D) μ := by
  funext d; apply propext; constructor
  · exact star_102_861 μ d
  · rintro ⟨a, ha, had⟩
    obtain ⟨c, hac, hcd⟩ := bridge a d had
    exact ⟨c, ⟨a, ha, hac⟩, hcd⟩

/-- ✱102·863, a cardinal fibre remains fixed after any two type changes. -/
theorem star_102_863 (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀)
    (c₀ : Class C) (hc₀ : Nc d c₀) :
    SimilarityImage (A := C) (B := B) (SimilarityImage (Nc (A := A) d)) = Nc (A := B) d := by
  rw [similarityImage_nc d a₀ ha₀]
  exact star_102_81 d c₀ hc₀

/-- ✱102·87, changing through an intermediate type or directly gives the same fibre. -/
theorem star_102_87 (d : Class D) (c₀ : Class C) (hc₀ : Nc d c₀) :
    SimilarityImage (A := C) (B := B) (Nc (A := C) d) = Nc (A := B) d :=
  star_102_81 d c₀ hc₀

/-- ✱102·88, an existing typed similarity image is the target `Nc` fibre. -/
theorem star_102_88 (d : Class D) (a₀ : Class A) (ha₀ : Nc d a₀) :
    SimilarityImage (Nc (A := A) d) = Nc (A := B) d := similarityImage_nc d a₀ ha₀

end PM.Architecture.Star102ClosingKernel
