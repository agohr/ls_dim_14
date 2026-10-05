import QuaternionicSymmetry.QuaternionicProjectiveStandardSign
import QuaternionicSymmetry.QuaternionicManifoldStandardLocalOperator
import QuaternionicSymmetry.ContinuousSignRigidity

/-! The central sign relating two smooth standard lifts is locally constant. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardSignRigidity
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardAdjoint
  QuaternionicProjectiveStandardSign QuaternionicManifoldStandardLocalOperator
  QuaternionicManifoldLocalScalarLifts QuaternionicManifoldSignedLocalLifts
open scoped ContDiff Manifold Quaternion Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem localStandardOperator_eq_or_neg (i j : atlas E M) (q r : unitary ℍ)
    (x : M) (hq : x ∈ liftNeighborhood Q i j q)
    (hr : x ∈ liftNeighborhood Q i j r) :
    localStandardOperator S Q i j q x = localStandardOperator S Q i j r x ∨
    localStandardOperator S Q i j q x = -localStandardOperator S Q i j r x := by
  rw [localStandardOperator_eq S Q i j q x hq, localStandardOperator_eq S Q i j r x hr]
  apply standardActionL2_eq_or_neg_of_same_tangent
  rw [localProductLift_image, localProductLift_image]

theorem localStandardOperator_ne_zero (i j : atlas E M) (q : unitary ℍ)
    (x : M) (hx : x ∈ liftNeighborhood Q i j q) :
    localStandardOperator S Q i j q x ≠ 0 := by
  rw [localStandardOperator_eq S Q i j q x hx]
  intro h
  have hall (z : StandardSpace (E := E)) : z = 0 := by
    apply (standardActionL2 S (localProductLift S Q i j q x hx)).injective
    change (standardActionL2 S (localProductLift S Q i j q x hx)).toContinuousLinearMap z =
      (standardActionL2 S (localProductLift S Q i j q x hx)).toContinuousLinearMap 0
    rw [h]
    rfl
  obtain ⟨z, hz⟩ := exists_ne (0 : StandardSpace (E := E))
  exact hz (hall z)

theorem localStandardOperator_eventually_eq_or_neg (i j : atlas E M) (q r : unitary ℍ)
    (x : M) (hq : x ∈ liftNeighborhood Q i j q)
    (hr : x ∈ liftNeighborhood Q i j r) :
    localStandardOperator S Q i j q =ᶠ[𝓝 x] localStandardOperator S Q i j r ∨
    localStandardOperator S Q i j q =ᶠ[𝓝 x] (fun y => -localStandardOperator S Q i j r y) := by
  apply ContinuousSignRigidity.eventually_eq_or_neg
  · exact (smooth_localStandardOperator S Q i j q).continuousOn.continuousAt
      ((isOpen_liftNeighborhood Q i j q).mem_nhds hq)
  · exact (smooth_localStandardOperator S Q i j r).continuousOn.continuousAt
      ((isOpen_liftNeighborhood Q i j r).mem_nhds hr)
  · exact localStandardOperator_ne_zero S Q i j r x hr
  · filter_upwards [(isOpen_liftNeighborhood Q i j q).mem_nhds hq,
      (isOpen_liftNeighborhood Q i j r).mem_nhds hr] with y hyq hyr
    exact localStandardOperator_eq_or_neg S Q i j q r y hyq hyr

end
end QuaternionicSymmetry.QuaternionicManifoldStandardSignRigidity
