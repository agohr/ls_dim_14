import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTensorDescent
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChart

/-! Comparison of a centered genuine manifold chart with the fixed
base/projective-affine maps used in the all-chart tensor descent. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChart

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveScalarFiber
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem preferred_fixedChart_eq_extChartAt (z : SpinorBundleTotal Q)
    (w : SpinorBundleTotal Q) :
    fixedProjectiveChart Q z.1 (preferredProjectiveChartIndex z.2) w =
      projectiveTangentModelEquiv ((extChartAt productModel z) w) := by
  change fixedProjectiveChart Q z.1
      (preferredProjectiveChartIndex z.2) w =
      projectiveTangentModelEquiv
        ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) w)
  rw [chartAt_comp, FiberBundle.chartedSpace'_chartAt]
  simp only [fixedProjectiveChart, projectiveTangentModelEquiv_apply,
    OpenPartialHomeomorph.trans_apply,
    prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  change ((extChartAt 𝓘(ℝ, ℍ) z.1) w.1,
      ((projectiveChart 1 (preferredProjectiveChartIndex z.2))
        (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) w).2) 0) =
    ((extChartAt 𝓘(ℝ, ℍ) z.1) w.1,
      ((chartAt (Fin 1 → ℂ)
        (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).2)
        (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) w).2) 0)
  rw [preferred_localTriv Q z]
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChart
