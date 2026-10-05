import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartInverse
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualModelTensorSmooth

/-! At each total-space point, the independently defined pointwise
projective almost-complex operator is exactly the local tensor in the
genuine centered fixed affine chart. This is the center-value bridge;
arbitrary-chart tangent conjugacy follows from chart-transition covariance. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedTensor

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectivePreferredFixedChart
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  ComplexProjectiveTopology
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem preferred_fixedChart_value (z : SpinorBundleTotal Q) :
    fixedProjectiveChart Q z.1 (preferredProjectiveChartIndex z.2) z =
      (extChartAt 𝓘(ℝ, ℍ) z.1 z.1, preferredProjectiveScalar z.2) := by
  rw [preferred_fixedChart_eq_extChartAt Q z z]
  change projectiveTangentModelEquiv
    ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z) = _
  rw [preferred_total_chart_value Q z]
  rfl

theorem preferredLocalModel_eq_indexed (z : SpinorBundleTotal Q) :
    preferredLocalModel Q D z =
      indexedLocalTensor Q D (preferredProjectiveChartIndex z.2)
        z.1 (fixedProjectiveChart Q z.1
          (preferredProjectiveChartIndex z.2) z).1
          (fixedProjectiveChart Q z.1
            (preferredProjectiveChartIndex z.2) z).2 := by
  rw [preferred_fixedChart_value Q z]
  unfold preferredLocalModel indexedLocalTensor
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedTensor
