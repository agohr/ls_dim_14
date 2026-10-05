import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChartSmooth

/-! The corrected total Hopf differential satisfies the literal full
manifold chain rule in each fixed projective/raw twistor chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleMFDeriv

open scoped Manifold ContDiff Topology Quaternion
open FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveCorrectedBundleChartSmooth
  FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveFixedChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartCore
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

theorem correctedHopf_fixedChart_mfderiv_chain (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    (mfderiv sphereModel sphereModel (fixedRawChart Q p)
      (correctedSpinorSphereDiffeomorph Q z)).comp
      (mfderiv projectiveModel sphereModel
        (correctedSpinorSphereDiffeomorph Q) z) =
    (mfderiv 𝓘(ℝ, ℍ × ℂ) sphereModel (fixedCorrectedHopf i)
      (fixedProjectiveChart Q p i z)).comp
      (mfderiv projectiveModel 𝓘(ℝ, ℍ × ℂ)
        (fixedProjectiveChart Q p i) z) := by
  let f := correctedSpinorSphereDiffeomorph Q
  let c := fixedProjectiveChart Q p i z
  have hp : z.1 ∈ (sphereCore Q).baseSet (achart ℍ p) := by
    have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mp hz.1
    exact hp'
  have hRawSource : f z ∈
      ((sphereCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart ℍ p) _).mpr hp
  have hRaw : MDifferentiableAt sphereModel sphereModel
      (fixedRawChart Q p) (f z) :=
    ((fixedRawChart_smoothOn Q p).contMDiffAt
      (((sphereCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.open_source.mem_nhds
        hRawSource)).mdifferentiableAt (by simp)
  have hF : MDifferentiableAt projectiveModel sphereModel f z :=
    (correctedSpinorSphereDiffeomorph Q).contMDiff_toFun.mdifferentiableAt (by simp)
  have hC : MDifferentiableAt projectiveModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q p i) z :=
    (fixedProjectiveChart_smoothAt Q p i z hz).mdifferentiableAt (by simp)
  have hc : c ∈ FourDimensionalHalfSpinProjectiveFixedChartTarget.fixedChartTarget Q p i :=
    FourDimensionalHalfSpinProjectiveFixedChartTarget.fixedChart_mem_target Q p i z hz
  have hLocal : MDifferentiableAt 𝓘(ℝ, ℍ × ℂ) sphereModel
      (fixedCorrectedHopf i) c :=
    (fixedCorrectedHopf_smoothAt Q p i c hc).mdifferentiableAt (by simp)
  have hEq : (fixedRawChart Q p ∘ f) =ᶠ[𝓝 z]
      (fixedCorrectedHopf i ∘ fixedProjectiveChart Q p i) := by
    filter_upwards [(fixedChartSource_isOpen Q p i).mem_nhds hz] with w hw
    exact fixedRawChart_correctedHopf Q p i w hw
  have hDer := Filter.EventuallyEq.mfderiv_eq
    (I := projectiveModel) (I' := sphereModel) hEq
  rw [mfderiv_comp z hRaw hF, mfderiv_comp z hLocal hC] at hDer
  exact hDer

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleMFDeriv
