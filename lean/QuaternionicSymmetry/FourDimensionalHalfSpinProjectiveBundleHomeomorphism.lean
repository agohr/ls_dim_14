import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveInverseContinuous

/-! The independently topologized associated projective half-spin bundle
and actual smooth twistor-sphere bundle are fiberwise Hopf-homeomorphic. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleHomeomorphism

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveForwardContinuous
  FourDimensionalHalfSpinProjectiveInverseContinuous
  ManifoldTwistorSphereCore

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def spinorSphereHomeomorph :
    SpinorBundleTotal Q ≃ₜ SphereBundleTotal Q where
  toEquiv := spinorSphereEquiv Q
  continuous_toFun := spinorToSphere_continuous Q
  continuous_invFun := sphereToSpinor_continuous Q

theorem spinorSphereHomeomorph_projection (p : SpinorBundleTotal Q) :
    (spinorSphereHomeomorph Q p).1 = p.1 := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleHomeomorphism
