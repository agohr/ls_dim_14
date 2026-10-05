import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointLocal
import Mathlib.Topology.VectorBundle.Basic

/-! A genuine global adjoint vector bundle on the original adapted tangent
atlas. Pointwise `Sp(n)×Sp(1)` lifts are used only to define its coordinate
changes; local smooth lifts prove continuity and independence of choices. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointCore

open VectorBundleFrameTransitions
  QuaternionicManifoldPointwiseLifts
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldSignedLocalLifts
  QuaternionicManifoldProjectiveAdjointLocal
  QuaternionicProjectiveStandardAdjoint
  QuaternionicUnitScalarIsometries
open scoped ContDiff Manifold Topology Bundle Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

abbrev StdEnd := QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)

def projectiveCoordChange (i j : atlas E M) (y : M) :
    StdEnd (E := E) →L[ℝ] StdEnd (E := E) := by
  classical
  exact if hy : y ∈ overlap Q i j then
    standardAdjoint S (chosenLift S Q i j y hy.1 hy.2)
  else 0

theorem projectiveCoordChange_on_overlap (i j : atlas E M) (y : M)
    (hi : y ∈ Q.frames.adaptedCore.baseSet i)
    (hj : y ∈ Q.frames.adaptedCore.baseSet j) :
    projectiveCoordChange S Q i j y =
      standardAdjoint S (chosenLift S Q i j y hi hj) := by
  classical
  simp only [projectiveCoordChange, dif_pos (show y ∈ overlap Q i j from ⟨hi, hj⟩)]

theorem projectiveCoordChange_eq_local (i j : atlas E M)
    (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    projectiveCoordChange S Q i j y = localAdjointOperator S Q i j q y := by
  rw [projectiveCoordChange_on_overlap S Q i j y hy.1.1 hy.1.2,
    localAdjointOperator_eq S Q i j q y hy]
  apply standardAdjoint_eq_of_same_tangent S
  rw [chosenLift_image, localProductLift_image]

theorem continuousOn_projectiveCoordChange (i j : atlas E M) :
    ContinuousOn (projectiveCoordChange S Q i j) (overlap Q i j) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  obtain ⟨q, hqx, hopen, _, _⟩ :=
    exists_local_scalar_lift Q S i j x hx.1 hx.2
  have hlocal := (continuousOn_localAdjointOperator S Q i j q).continuousAt
    (hopen.mem_nhds hqx)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hqx] with y hy
  exact projectiveCoordChange_eq_local S Q i j q y hy

theorem projectiveCoordChange_self (i : atlas E M) (y : M)
    (hi : y ∈ Q.frames.adaptedCore.baseSet i)
    (B : StdEnd (E := E)) :
    projectiveCoordChange S Q i i y B = B := by
  rw [projectiveCoordChange_on_overlap S Q i i y hi hi]
  have hfix : fixedTransitionNormalizer S Q i i y hi hi = 1 := by
    have h := fixedTransition_cocycle S Q i i i y hi hi hi
    exact mul_left_cancel (by simpa only [mul_one] using h)
  have hp : symplecticProductAction S (chosenLift S Q i i y hi hi) = 1 := by
    rw [chosenLift_image, hfix]
  exact standardAdjoint_kernel S _ hp B

theorem projectiveCoordChange_comp (i j k : atlas E M) (y : M)
    (hi : y ∈ Q.frames.adaptedCore.baseSet i)
    (hj : y ∈ Q.frames.adaptedCore.baseSet j)
    (hk : y ∈ Q.frames.adaptedCore.baseSet k)
    (B : StdEnd (E := E)) :
    projectiveCoordChange S Q j k y
      (projectiveCoordChange S Q i j y B) =
      projectiveCoordChange S Q i k y B := by
  rw [projectiveCoordChange_on_overlap S Q i j y hi hj,
    projectiveCoordChange_on_overlap S Q j k y hj hk,
    projectiveCoordChange_on_overlap S Q i k y hi hk]
  let pjk := chosenLift S Q j k y hj hk
  let pij := chosenLift S Q i j y hi hj
  let pik := chosenLift S Q i k y hi hk
  have hsame : symplecticProductAction S (pjk * pij) =
      symplecticProductAction S pik := by
    rw [map_mul, chosenLift_image, chosenLift_image,
      chosenLift_image, fixedTransition_cocycle]
  calc
    standardAdjoint S pjk (standardAdjoint S pij B) =
        standardAdjoint S (pjk * pij) B :=
      (standardAdjoint_mul S pjk pij B).symm
    _ = standardAdjoint S pik B :=
      congrArg (fun T : StdEnd (E := E) →L[ℝ] StdEnd (E := E) => T B)
        (standardAdjoint_eq_of_same_tangent S _ _ hsame)

/-- The original adapted tangent atlas, with no global product lifts on its
old overlaps, carries the genuine standard projective adjoint bundle core. -/
def projectiveCore :
    VectorBundleCore ℝ M (StdEnd (E := E)) (atlas E M) where
  baseSet := Q.frames.adaptedCore.baseSet
  isOpen_baseSet := Q.frames.adaptedCore.isOpen_baseSet
  indexAt := Q.frames.adaptedCore.indexAt
  mem_baseSet_at := Q.frames.adaptedCore.mem_baseSet_at
  coordChange := projectiveCoordChange S Q
  coordChange_self := projectiveCoordChange_self S Q
  continuousOn_coordChange i j := by
    simpa only [overlap] using continuousOn_projectiveCoordChange S Q i j
  coordChange_comp i j k y hy B :=
    projectiveCoordChange_comp S Q i j k y hy.1.1 hy.1.2 hy.2 B

def projectiveVectorBundle := (projectiveCore S Q).vectorBundle

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointCore
