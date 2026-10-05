import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
import QuaternionicSymmetry.ManifoldTwistorSphereBundle

/-! The rotating quaternionic rank-three sphere has the same coefficient
transitions under constant metric homothety. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistor
open ManifoldQuaternionicMetric ManifoldQuaternionicHomothetyReduction
open ManifoldTwistorSphereBundle VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem rankThreeCoordChange_rescale (s : ℝ) (hs : s ≠ 0)
    (i j : atlas E M) (x : M) :
    (rescaleMetric Q s hs).reduction.rankThreeCoordChange i j x =
      Q.reduction.rankThreeCoordChange i j x := by
  ext a t
  simp only [QuaternionicFrameReduction.rankThreeCoordChange_apply,
    adjointCoordChange_apply]
  simp only [rescaleMetric, rescaleReduction,
    ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
    ManifoldQuaternionicHomothetyFrames.rescale_coordChange]

theorem sphereTransition_rescale (s : ℝ) (hs : s ≠ 0)
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    sphereTransition (rescaleMetric Q s hs) i j x hi hj =
      sphereTransition Q i j x hi hj := by
  funext a
  apply Subtype.ext
  exact congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) => L a.1)
    (rankThreeCoordChange_rescale Q s hs i j x)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistor
