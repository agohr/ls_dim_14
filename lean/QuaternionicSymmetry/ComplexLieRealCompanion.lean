import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! The same complex self-model atlas of a complex Lie group is a real
smooth Lie atlas. This is scalar restriction, not a new atlas. -/

namespace QuaternionicSymmetry.ComplexLieRealCompanion

open Manifold ManifoldComplexHolomorphicFactorization
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [TopologicalSpace G] [ChartedSpace V G]

theorem realManifold [IsManifold 𝓘(ℂ,V) ∞ G] :
    IsManifold 𝓘(ℝ,V) ∞ G := by
  apply isManifold_of_contDiffOn 𝓘(ℝ,V) ∞ G
  intro e e' he he'
  have hc := (inferInstance : IsManifold 𝓘(ℂ,V) ∞ G).compatible he he'
  exact hc.1.restrict_scalars ℝ

theorem realLieGroup [Group G] [LieGroup 𝓘(ℂ,V) ∞ G] :
    LieGroup 𝓘(ℝ,V) ∞ G := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hc : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ∞
        (fun p : G × G => p.1 * p.2) := contMDiff_mul 𝓘(ℂ,V) ∞
    rw [← modelWithCornersSelf_prod] at hc ⊢
    letI : ChartedSpace (V × V) (G × G) := prodChartedSpace V G V G
    letI : IsManifold 𝓘(ℂ,V × V) ∞ (G × G) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G G
    letI : IsManifold 𝓘(ℝ,V × V) ∞ (G × G) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G G
    exact holomorphic_is_real_smooth (E := V × V) (F := V) hc
  · exact holomorphic_is_real_smooth (E := V) (F := V)
      (contMDiff_inv 𝓘(ℂ,V) ∞ :
        ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (fun g : G => g⁻¹))

end
end QuaternionicSymmetry.ComplexLieRealCompanion
