import QuaternionicSymmetry.ManifoldQuaternionicHomothetyFrames
import QuaternionicSymmetry.ManifoldQuaternionicMetric

/-! A constant metric homothety retains the actual rotating quaternionic span. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicReduction ManifoldQuaternionicHomothetyFrames
open ManifoldQuaternionicMetric VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (Q : SmoothQuaternionicHermitianTangent (I := I) (M := M) (n := n))

def rescaleReduction (s : ℝ) (hs : s ≠ 0) :
    SmoothAlmostQuaternionicTangent (I := I) (M := M) (n := n) where
  frames := rescale Q.frames s hs
  reduction := {
    Q := Q.reduction.Q
    generator_transport := by
      intro i j x hi hj t
      have h := Q.reduction.generator_transport i j x hi hj t
      simpa only [VectorBundleFrameTransitions.adjointCoordChange_apply,
        TangentFrameGauge.adaptedCore, transitionAtlas,
        rescale_coordChange] using h }

def rescaleMetric (s : ℝ) (hs : s ≠ 0) :
    SmoothQuaternionicHermitianTangent (I := I) (M := M) (n := n) where
  toSmoothAlmostQuaternionicTangent := rescaleReduction Q s hs
  transition_inner := by
    intro i j x hi hj v w
    simpa only [rescaleReduction, rescale_coordChange] using
      Q.transition_inner i j x hi hj v w

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyReduction
