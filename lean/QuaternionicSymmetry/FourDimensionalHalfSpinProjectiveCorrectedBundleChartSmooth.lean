import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChart
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTarget

/-! The explicit corrected-Hopf map between fixed projective and raw sphere
chart models is smooth on the exact independently constructed chart target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChartSmooth

open scoped Manifold ContDiff Topology Quaternion
open FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ManifoldTwistorSphereCore
  ManifoldTwistorGlobalAlmostComplex
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev projectiveModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev sphereModel := 𝓘(ℝ, ℍ).prod (𝓡 2)

theorem fixedCorrectedHopf_chart_inv (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    fixedCorrectedHopf i c =
      fixedRawChart Q p
        (correctedSpinorSphereDiffeomorph Q (fixedProjectiveChartInv Q p i c)) := by
  let z := fixedProjectiveChartInv Q p i c
  have hz : z ∈ fixedChartSource Q p i := fixedChartInv_mem_source Q p i c hc
  have h := fixedRawChart_correctedHopf Q p i z hz
  rw [fixedChartInv_right_target Q p i c hc] at h
  exact h.symm

theorem fixedCorrectedHopf_smoothAt (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    ContMDiffAt 𝓘(ℝ, ℍ × ℂ) sphereModel ∞
      (fixedCorrectedHopf i) c := by
  let z := fixedProjectiveChartInv Q p i c
  have hz : z ∈ fixedChartSource Q p i := fixedChartInv_mem_source Q p i c hc
  have hbase : z.1 ∈ (sphereCore Q).baseSet (achart ℍ p) := by
    have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mp hz.1
    exact hp'
  have hsource : correctedSpinorSphereDiffeomorph Q z ∈
      ((sphereCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart ℍ p) _).mpr hbase
  have hraw : ContMDiffAt sphereModel sphereModel ∞
      (fixedRawChart Q p) (correctedSpinorSphereDiffeomorph Q z) :=
    (fixedRawChart_smoothOn Q p).contMDiffAt
      (((sphereCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.open_source.mem_nhds hsource)
  have hcomp : ContMDiffAt 𝓘(ℝ, ℍ × ℂ) sphereModel ∞
      (fun r => fixedRawChart Q p
        (correctedSpinorSphereDiffeomorph Q (fixedProjectiveChartInv Q p i r))) c :=
    hraw.comp c ((correctedSpinorSphereDiffeomorph Q).contMDiff_toFun.contMDiffAt.comp c
      (fixedProjectiveChartInv_smoothAt Q p i c hc))
  have hEq : (fun r => fixedRawChart Q p
      (correctedSpinorSphereDiffeomorph Q (fixedProjectiveChartInv Q p i r))) =ᶠ[𝓝 c]
        fixedCorrectedHopf i := by
    filter_upwards [(fixedChartTarget_isOpen Q p i).mem_nhds hc] with r hr
    exact (fixedCorrectedHopf_chart_inv Q p i r hr).symm
  exact hcomp.congr_of_eventuallyEq hEq.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChartSmooth
