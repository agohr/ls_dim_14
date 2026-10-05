import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistor
import QuaternionicSymmetry.ManifoldTwistorSphereCore

/-! Identity of the genuine twistor sphere bundle cores under metric scaling. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistor ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private theorem fiberBundleCore_ext {ι B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] (Z W : FiberBundleCore ι B F)
    (hb : Z.baseSet = W.baseSet) (hi : Z.indexAt = W.indexAt)
    (hc : Z.coordChange = W.coordChange) : Z = W := by
  cases Z with
  | mk b ob ix mi cc self cont comp =>
    cases W with
    | mk b' ob' ix' mi' cc' self' cont' comp' =>
      cases hb
      cases hi
      cases hc
      rfl

theorem euclideanSphereCoordChange_rescale (s : ℝ) (hs : s ≠ 0)
    (i j : atlas E M) (x : M) (a : ManifoldTwistorCoefficientSphere.geometricSphere) :
    euclideanSphereCoordChange (rescaleMetric Q s hs) i j x a =
      euclideanSphereCoordChange Q i j x a := by
  classical
  unfold euclideanSphereCoordChange
  have hbase (k : atlas E M) :
      (rescaleMetric Q s hs).frames.adaptedCore.baseSet k =
        Q.frames.adaptedCore.baseSet k := rfl
  simp only [hbase]
  by_cases h : x ∈ Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j
  · simp only [dif_pos h]
    exact congrArg ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph
      (congrArg (fun f => f (ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.symm a))
        (sphereTransition_rescale Q s hs i j x h.1 h.2))
  · simp only [dif_neg h]

theorem sphereCore_rescale (s : ℝ) (hs : s ≠ 0) :
    sphereCore (rescaleMetric Q s hs) = sphereCore Q := by
  apply fiberBundleCore_ext
  · rfl
  · rfl
  · funext i j x a
    exact euclideanSphereCoordChange_rescale Q s hs i j x a


end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore
