import Principia.Architecture.Star233AnalyticArchitecture
import Principia.FirstEdition.Volume2.Star233Source

namespace PM.Architecture.Star233OpeningKernel
open PM.Architecture.Star233AnalyticArchitecture

def lmx (limax : PFunction β γ) (sec : PFunction α β) : PFunction α γ :=
  compose limax sec
def intervalMap (limax : PFunction β γ) (sec : PFunction α β)
    (ray : PFunction δ α) : PFunction δ γ := compose (lmx limax sec) ray

theorem star_233_01 : lmx limax sec = compose limax sec := rfl
theorem star_233_02 : intervalMap limax sec ray = compose (lmx limax sec) ray := rfl
theorem star_233_1 : Graph (lmx limax sec) x y ↔
    ∃ z, Graph sec x z ∧ Graph limax z y := by
  cases h : sec x <;> simp [Graph, lmx, compose, h]
theorem star_233_101 : Graph (lmx limax sec) x y ↔
    (sec x).bind limax = some y := Iff.rfl
theorem star_233_102 : ExistsValue (lmx limax sec) x ↔
    ∃ z y, Graph sec x z ∧ Graph limax z y := exists_compose_iff

theorem star_233_103 : Graph (lmx limax sec) x y →
    Graph (lmx limax sec) x z → y = z := graph_functional

end PM.Architecture.Star233OpeningKernel
