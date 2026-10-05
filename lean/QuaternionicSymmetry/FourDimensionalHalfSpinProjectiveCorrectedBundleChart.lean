import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentLeftInverse
import QuaternionicSymmetry.ManifoldTwistorFixedRawChart

/-! Literal raw sphere-chart expression of the corrected global Hopf map
in every genuine fixed affine projective chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChart

open scoped Manifold ContDiff Quaternion
open FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorGlobalAlmostComplex
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorSphereTotalAntipodalChart
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def fixedCorrectedHopf (i : Fin 2) (c : ℍ × ℂ) :
    ℍ × geometricSphere :=
  (c.1, correctedHopf (indexedSourcePoint i c.2))

theorem fixedRawChart_correctedHopf (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    fixedRawChart Q p (correctedSpinorSphereDiffeomorph Q z) =
      fixedCorrectedHopf i (fixedProjectiveChart Q p i z) := by
  let Zp := projectiveSpinorCore Q
  let Zs := sphereCore Q
  have hp : z.1 ∈ Zp.baseSet (achart ℍ p) :=
    (Zp.mem_localTriv_source (achart ℍ p) z).mp hz.1
  have hlocal := localTriv_hopf Q (achart ℍ p) z hp
  have hs : (spinorToSphere Q z).1 ∈ Zs.baseSet (achart ℍ p) := hp
  have hanti := sphereAntipodal_localTriv Q (achart ℍ p)
    (spinorToSphere Q z) hs
  apply Prod.ext
  · rfl
  · change (Zs.localTriv (achart ℍ p)
        (sphereAntipodal Q (spinorToSphere Q z))).2 =
        correctedHopf (indexedSourcePoint i
          (((projectiveChart 1 i) ((Zp.localTriv (achart ℍ p) z).2)) 0))
    rw [congrArg Prod.snd hanti, hlocal]
    rw [indexedSourcePoint_chart_left i _ hz.2]
    rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleChart
