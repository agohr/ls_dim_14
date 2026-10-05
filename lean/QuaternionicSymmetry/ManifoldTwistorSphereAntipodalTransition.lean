import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalWeight
import QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative

/-! Antipodal covariance for the genuine rank-three sphere transitions. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereAntipodalTransition

open scoped Manifold ContDiff
open ManifoldTwistorSphereBundle ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldTwistorSphereAntipodalDerivative

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem sphereTransition_antipodal
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    sphereTransition Q i j x hi hj (coefficientAntipodal a) =
      coefficientAntipodal (sphereTransition Q i j x hi hj a) := by
  apply Subtype.ext
  change Q.reduction.rankThreeCoordChange i j x (-a.1) =
    -(Q.reduction.rankThreeCoordChange i j x a.1)
  exact map_neg _ _

theorem euclideanSphereCoordChange_antipodal
    (i j : atlas E M) (x : M) (a : geometricSphere) :
    euclideanSphereCoordChange Q i j x (geometricAntipodal a) =
      geometricAntipodal (euclideanSphereCoordChange Q i j x a) := by
  classical
  by_cases h : x ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j
  · simp only [euclideanSphereCoordChange, dif_pos h]
    have hanti : coefficientSphereHomeomorph.symm (geometricAntipodal a) =
        coefficientAntipodal (coefficientSphereHomeomorph.symm a) := by
      apply Subtype.ext
      rfl
    rw [hanti, sphereTransition_antipodal]
    apply Subtype.ext
    rfl
  · simp only [euclideanSphereCoordChange, dif_neg h]

end
end QuaternionicSymmetry.ManifoldTwistorSphereAntipodalTransition
