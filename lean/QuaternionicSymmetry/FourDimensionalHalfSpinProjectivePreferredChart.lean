import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCore

/-! The fiber coordinate chosen by the genuine smooth projective-bundle
atlas at a total-space point is the very CP¹ affine chart used by the
pointwise tensor definition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChart

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinActualTransitionSmooth
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem preferred_localTriv (z : SpinorBundleTotal Q) :
    (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).2 = z.2 := by
  rw [(projectiveSpinorCore Q).localTriv_apply]
  change spinorCoordChange Q (achart ℍ z.1) (achart ℍ z.1)
    (z.1,z.2) = z.2
  exact spinorCoordChange_self Q (achart ℍ z.1) z.1
    ((projectiveSpinorCore Q).mem_baseSet_at z.1) z.2

theorem selected_projective_chart (s : FourDimensionalHalfSpinProjective.ProjectiveSpinor) :
    chartAt (Fin 1 → ℂ) s =
      projectiveChart 1 (preferredProjectiveChartIndex s) := rfl

theorem preferred_total_chart_fiber (z : SpinorBundleTotal Q) :
    ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z).2 =
      (projectiveChart 1 (preferredProjectiveChartIndex z.2)) z.2 := by
  rw [chartAt_comp, FiberBundle.chartedSpace'_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply,
    prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  change (chartAt (Fin 1 → ℂ)
      (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).2)
      (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).2 = _
  rw [preferred_localTriv Q z]
  rw [selected_projective_chart]

theorem preferred_total_chart_base (z : SpinorBundleTotal Q) :
    ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z).1 =
      (chartAt ℍ z.1) z.1 := by
  rw [chartAt_comp, FiberBundle.chartedSpace'_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply,
    prodChartedSpace_chartAt]
  change (chartAt ℍ
      (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).1)
      (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).1 = _
  rw [(projectiveSpinorCore Q).localTriv_apply]

theorem preferred_total_chart_value (z : SpinorBundleTotal Q) :
    (chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z =
      ((chartAt ℍ z.1) z.1,
        (projectiveChart 1 (preferredProjectiveChartIndex z.2)) z.2) := by
  exact Prod.ext (preferred_total_chart_base Q z)
    (preferred_total_chart_fiber Q z)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChart
