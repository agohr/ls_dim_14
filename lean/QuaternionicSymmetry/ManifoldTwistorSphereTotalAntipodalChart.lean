import QuaternionicSymmetry.ManifoldTwistorSphereAntipodalTransition

/-! The actual total-space twistor antipode is fiberwise negation in every
genuine sphere-bundle trivialization, not just in one preferred fiber. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalChart

open scoped Manifold ContDiff
open ManifoldTwistorSphereBundle ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorSphereAntipodalTransition

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem sphereAntipodal_localTriv
    (i : atlas E M) (z : SphereBundleTotal Q)
    (hz : z.1 ∈ (sphereCore Q).baseSet i) :
    (sphereCore Q).localTriv i (sphereAntipodal Q z) =
      (z.1, geometricAntipodal (((sphereCore Q).localTriv i z).2)) := by
  let Z := sphereCore Q
  rw [Z.localTriv_apply, Z.localTriv_apply]
  apply Prod.ext
  · rfl
  · change euclideanSphereCoordChange Q (Z.indexAt z.1) i z.1
        (geometricAntipodal z.2) =
      geometricAntipodal
        (euclideanSphereCoordChange Q (Z.indexAt z.1) i z.1 z.2)
    exact euclideanSphereCoordChange_antipodal Q _ _ _ _

end
end QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalChart
