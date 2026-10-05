import QuaternionicSymmetry.SmoothLieGroupEquivBracket

/-! The genuine Lie-algebra equivalence induced by a holomorphic Lie-group
diffeomorphism, with bracket preservation proved through invariant fields. -/

namespace QuaternionicSymmetry.SmoothLieGroupEquivLieAlgebra

open SmoothLieGroupEquivBracket
open scoped Manifold ContDiff
noncomputable section

variable {V G H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V]
  [TopologicalSpace G] [TopologicalSpace H]
  [ChartedSpace V G] [ChartedSpace V H] [Group G] [Group H]
  [LieGroup 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ H]
  [LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) G]
  [LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) H]

/-- Actual identity differential as a complex Lie-algebra equivalence. -/
def mfderiv_one_lieEquiv
    (Φ : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) G H ∞)
    (hOne : Φ (1 : G) = 1)
    (hMul : ∀ g x : G, Φ (g*x) = Φ g * Φ x) :
    GroupLieAlgebra 𝓘(ℂ,V) G ≃ₗ⁅ℂ⁆ GroupLieAlgebra 𝓘(ℂ,V) H := by
  let d : GroupLieAlgebra 𝓘(ℂ,V) G ≃L[ℂ]
      GroupLieAlgebra 𝓘(ℂ,V) H := by
    simpa only [hOne] using Φ.mfderivToContinuousLinearEquiv (by simp) (1 : G)
  have hMap : ∀ v w : GroupLieAlgebra 𝓘(ℂ,V) G,
      d ⁅v,w⁆ = ⁅d v,d w⁆ := by
    intro v w
    simpa only [d, hOne] using mfderiv_one_map_lie Φ hOne hMul v w
  exact { d.toLinearEquiv with map_lie' := fun {v w} => hMap v w }

end
end QuaternionicSymmetry.SmoothLieGroupEquivLieAlgebra
