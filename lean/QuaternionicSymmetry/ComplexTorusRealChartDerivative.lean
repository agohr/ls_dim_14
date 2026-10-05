import QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-! The actual open-coordinate chart of `(ℂˣ)^r` has identity real
differential in the singleton charted-space structure. -/

namespace QuaternionicSymmetry.ComplexTorusRealChartDerivative

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

theorem torusVal_mfderiv_eq_id (r : ℕ) (z : ComplexTorus r) :
    mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,Fin r → ℂ)
      (torusVal r) z = ContinuousLinearMap.id ℝ (Fin r → ℂ) := by
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  have hchart : (chartAt (Fin r → ℂ) z : ComplexTorus r → Fin r → ℂ) =
      torusVal r :=
    (torusVal_isOpenEmbedding r).singletonChartedSpace_chartAt_eq
  rw [← hchart]
  rw [mfderiv_chartAt_eq_tangentCoordChange
    (I := 𝓘(ℝ,Fin r → ℂ)) (mem_chart_source (Fin r → ℂ) z)]
  apply ContinuousLinearMap.ext
  intro v
  simpa using tangentCoordChange_self
    (I := 𝓘(ℝ,Fin r → ℂ)) (v := v) (mem_extChartAt_source z)

end
end QuaternionicSymmetry.ComplexTorusRealChartDerivative
