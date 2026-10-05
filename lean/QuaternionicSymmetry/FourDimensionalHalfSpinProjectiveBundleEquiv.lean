import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveManifold

/-! The literal fiberwise Hopf map between the independently constructed
projective half-spin bundle and the pre-existing geometric twistor sphere
bundle. At this stage the total map is a bijection with exact local-chart
formula; total-space continuity and smoothness follow separately. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleEquiv

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinActualTransitionSmooth
  FourDimensionalHalfSpinHopfDiffeomorph
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinProjective
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def spinorToSphere (p : SpinorBundleTotal Q) : SphereBundleTotal Q :=
  ⟨p.1, projectiveHopfGeometric p.2⟩

def sphereToSpinor (p : SphereBundleTotal Q) : SpinorBundleTotal Q :=
  ⟨p.1, projectiveHopfGeometricHomeomorph.symm p.2⟩

def spinorSphereEquiv : SpinorBundleTotal Q ≃ SphereBundleTotal Q where
  toFun := spinorToSphere Q
  invFun := sphereToSpinor Q
  left_inv p := by
    apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      exact projectiveHopfGeometricHomeomorph.symm_apply_apply p.2
  right_inv p := by
    apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      exact projectiveHopfGeometricHomeomorph.apply_symm_apply p.2

theorem localTriv_hopf (i : atlas ℍ M) (p : SpinorBundleTotal Q)
    (hi : p.1 ∈ (projectiveSpinorCore Q).baseSet i) :
    ((sphereCore Q).localTriv i (spinorToSphere Q p)).2 =
      projectiveHopfGeometric
        (((projectiveSpinorCore Q).localTriv i p).2) := by
  let Z := projectiveSpinorCore Q
  have hidx : p.1 ∈ Z.baseSet (Z.indexAt p.1) := Z.mem_baseSet_at _
  rw [(sphereCore Q).localTriv_apply, Z.localTriv_apply]
  change euclideanSphereCoordChange Q (Z.indexAt p.1) i p.1
      (projectiveHopfGeometric p.2) =
    projectiveHopfGeometric
      (spinorCoordChange Q (Z.indexAt p.1) i (p.1,p.2))
  exact (hopf_transition_eq Q (Z.indexAt p.1) i (p.1,p.2)
    ⟨hidx,hi⟩).symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleEquiv
