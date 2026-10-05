import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleInverseSmooth

/-! The explicit fiberwise Hopf comparison is a real-smooth diffeomorphism
between independently constructed associated projective and sphere bundles.
Its vertical complex sign is separately certified and is not suppressed here. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleDiffeomorph

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveBundleHomeomorphism
  FourDimensionalHalfSpinProjectiveBundleSmooth
  FourDimensionalHalfSpinProjectiveBundleInverseSmooth
  FourDimensionalHalfSpinProjectiveManifold
  ManifoldTwistorSphereCore

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def spinorSphereDiffeomorph :
    Diffeomorph (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ))
      (𝓘(ℝ, ℍ).prod (𝓡 2)) (SpinorBundleTotal Q) (SphereBundleTotal Q) ∞ :=
  { toEquiv := (spinorSphereHomeomorph Q).toEquiv
    contMDiff_toFun := spinorToSphere_contMDiff Q
    contMDiff_invFun := sphereToSpinor_contMDiff Q }

theorem spinorSphereDiffeomorph_projection (p : SpinorBundleTotal Q) :
    (spinorSphereDiffeomorph Q p).1 = p.1 := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleDiffeomorph
