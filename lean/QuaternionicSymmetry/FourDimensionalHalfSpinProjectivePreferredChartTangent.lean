import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChart

/-! The selected genuine total-space chart has identity manifold derivative
at its center in the actual tangent model. Together with the exact chart
value, this anchors the pointwise projective tensor in the independent
bundle atlas rather than in a transported sphere chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChartTangent

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectivePreferredChart

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem preferred_total_chart_mfderiv (z : SpinorBundleTotal Q) :
    mfderiv productModel productModel
      (chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z =
        ContinuousLinearMap.id ℝ
          (TangentSpace productModel z) := by
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source _ _)]
  apply ContinuousLinearMap.ext
  intro v
  exact tangentCoordChange_self
    (I := productModel) (x := z) (z := z) (v := v)
      (mem_extChartAt_source z)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChartTangent
