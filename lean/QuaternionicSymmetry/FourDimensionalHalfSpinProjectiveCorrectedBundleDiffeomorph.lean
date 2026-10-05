import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleDiffeomorph
import QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalSmooth
import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalEquivariance
import QuaternionicSymmetry.ManifoldTwistorCorrectedHopf

/-! The antipodally corrected Hopf comparison is a genuine diffeomorphism
between the independently constructed total-space atlases. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph

open scoped Manifold ContDiff Quaternion
open FourDimensionalHalfSpinProjectiveBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveManifold
  ManifoldTwistorSphereCore
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldQuaternionicTwistorAntipodalEquivariance
  ManifoldTwistorSphereTotalAntipodalSmooth
  ManifoldTwistorCorrectedHopf

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev projectiveModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev sphereModel := 𝓘(ℝ, ℍ).prod (𝓡 2)

def sphereTotalAntipodalDiffeomorph :
    Diffeomorph sphereModel sphereModel (SphereBundleTotal Q)
      (SphereBundleTotal Q) ∞ where
  toFun := sphereAntipodal Q
  invFun := sphereAntipodal Q
  left_inv := sphereAntipodal_involutive Q
  right_inv := sphereAntipodal_involutive Q
  contMDiff_toFun := sphereAntipodal_contMDiff Q
  contMDiff_invFun := sphereAntipodal_contMDiff Q

def correctedSpinorSphereDiffeomorph :
    Diffeomorph projectiveModel sphereModel (SpinorBundleTotal Q)
      (SphereBundleTotal Q) ∞ :=
  (spinorSphereDiffeomorph Q).trans (sphereTotalAntipodalDiffeomorph Q)

theorem correctedSpinorSphereDiffeomorph_base (z : SpinorBundleTotal Q) :
    (correctedSpinorSphereDiffeomorph Q z).1 = z.1 := rfl

theorem correctedSpinorSphereDiffeomorph_fiber (z : SpinorBundleTotal Q) :
    (correctedSpinorSphereDiffeomorph Q z).2 = correctedHopf z.2 := by
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
