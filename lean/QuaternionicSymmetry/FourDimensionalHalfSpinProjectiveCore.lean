import QuaternionicSymmetry.FourDimensionalHalfSpinActualTransitionSmooth

/-! An actual CP¹ fiber-bundle core over the quaternionic four-manifold,
whose transition functions are the literal projective half-spin matrices.
Its overlap regularity is inherited from the independently checked smooth
Hopf comparison; no global spinor vector bundle is chosen. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCore

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinActualTransitionSmooth
  FourDimensionalHalfSpinHopfDiffeomorphPackage
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinProjective
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem spinorCoordChange_self (i : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (p : ProjectiveSpinor) :
    spinorCoordChange Q i i (x,p) = p := by
  apply projectiveHopfGeometricDiffeomorph.injective
  have hp : x ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet i := ⟨hi,hi⟩
  change projectiveHopfGeometric (spinorCoordChange Q i i (x,p)) =
    projectiveHopfGeometric p
  rw [hopf_transition_eq Q i i (x,p) hp]
  exact euclideanSphereCoordChange_self Q i x hi (projectiveHopfGeometric p)

theorem spinorCoordChange_comp (i j k : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) (p : ProjectiveSpinor) :
    spinorCoordChange Q j k
        (x, spinorCoordChange Q i j (x,p)) =
      spinorCoordChange Q i k (x,p) := by
  apply projectiveHopfGeometricDiffeomorph.injective
  have hij : x ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j := ⟨hi,hj⟩
  have hjk : x ∈ Q.frames.adaptedCore.baseSet j ∩
      Q.frames.adaptedCore.baseSet k := ⟨hj,hk⟩
  have hik : x ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet k := ⟨hi,hk⟩
  change projectiveHopfGeometric
      (spinorCoordChange Q j k (x, spinorCoordChange Q i j (x,p))) =
    projectiveHopfGeometric (spinorCoordChange Q i k (x,p))
  rw [hopf_transition_eq Q j k _ hjk,
    hopf_transition_eq Q i j _ hij,
    hopf_transition_eq Q i k _ hik]
  exact euclideanSphereCoordChange_comp Q i j k x hi hj hk
    (projectiveHopfGeometric p)

/-- The projectivized half-spin bundle is constructed directly from the
checked literal CP¹ transition cocycle, not by transporting the sphere
bundle's total-space topology. -/
def projectiveSpinorCore : FiberBundleCore (atlas ℍ M) M ProjectiveSpinor where
  baseSet := Q.frames.adaptedCore.baseSet
  isOpen_baseSet := Q.frames.adaptedCore.isOpen_baseSet
  indexAt := Q.frames.adaptedCore.indexAt
  mem_baseSet_at := Q.frames.adaptedCore.mem_baseSet_at
  coordChange i j x p := spinorCoordChange Q i j (x,p)
  coordChange_self i x hi p := spinorCoordChange_self Q i x hi p
  continuousOn_coordChange i j := by
    exact (spinorCoordChange_contMDiffOn Q i j).continuousOn
  coordChange_comp i j k x hx p :=
    spinorCoordChange_comp Q i j k x hx.1.1 hx.1.2 hx.2 p

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCore
