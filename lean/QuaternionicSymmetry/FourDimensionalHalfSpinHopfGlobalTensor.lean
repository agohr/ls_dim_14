import QuaternionicSymmetry.FourDimensionalHalfSpinHopfFixedGlobalTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChart

/-! The independently constructed global projective almost-complex
tensor and the genuine Levi-Civita sphere-bundle tensor are intertwined
by the actual corrected Hopf diffeomorphism on every total-space tangent
fiber. The proof selects a genuine affine chart at each point and uses
the previously checked full derivative and chart-conjugacy identities. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfGlobalTensor

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfFixedGlobalTensor
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ManifoldTwistorGlobalAlmostComplex
  ManifoldQuaternionicMetric

noncomputable section

private abbrev projectiveModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev sphereModel := 𝓘(ℝ, ℍ).prod (𝓡 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- Genuine global tangent-level corrected Hopf intertwining, with no
transported definition of either almost-complex tensor. -/
theorem correctedHopf_globalTensor
    (z : SpinorBundleTotal Q) (v : TangentSpace projectiveModel z) :
    let f := correctedSpinorSphereDiffeomorph Q
    let F := mfderiv projectiveModel sphereModel f z
    F (FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS.tangentComplex Q D z v) =
      ManifoldTwistorGlobalAlmostComplex.tangentComplex Q D (f z) (F v) := by
  let i := preferredProjectiveChartIndex z.2
  have hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) z.1).source :=
    mem_extChartAt_source z.1
  have hi : ((projectiveSpinorCore Q).localTriv (achart ℍ z.1) z).2 ∈
      ComplexProjectiveTopology.affineDomain 1 i := by
    rw [preferred_localTriv Q z]
    exact preferredProjectiveChartIndex_mem z.2
  exact correctedHopf_fixedChart_globalTensor Q D z.1 i z hp hi v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfGlobalTensor
