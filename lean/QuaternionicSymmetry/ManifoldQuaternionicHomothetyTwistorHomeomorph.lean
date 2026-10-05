import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorHomeomorph
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

set_option maxHeartbeats 2000000 in
def sphereTotalHomeomorph (s : ℝ) (hs : s ≠ 0) :
    SphereBundleTotal (rescaleMetric Q s hs) ≃ₜ SphereBundleTotal Q := by
  let Z := sphereCore Q
  let W := sphereCore (rescaleMetric Q s hs)
  have h : Z = W := (sphereCore_rescale Q s hs).symm
  exact Eq.ndrec (motive := fun A : FiberBundleCore (atlas E M) M
      ManifoldTwistorCoefficientSphere.geometricSphere =>
        @Homeomorph A.TotalSpace Z.TotalSpace A.toTopologicalSpace Z.toTopologicalSpace)
      (Homeomorph.refl Z.TotalSpace) h

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorHomeomorph
