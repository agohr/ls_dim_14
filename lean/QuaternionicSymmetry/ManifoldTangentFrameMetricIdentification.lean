import QuaternionicSymmetry.ManifoldTangentFrameMetricOverlap

/-! A second source-free tangent-core calculation: pointwise preferred-
orthonormal local frames recover the underlying metric exactly from the
preferred adapted-frame coordinates. -/

namespace QuaternionicSymmetry.ManifoldTangentFrameMetricIdentification

open ManifoldQuaternionicReduction
open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [IsManifold I (∞ + 1) M]

theorem preferred_frame_metric_eq
    (F : TangentFrameGauge I (M := M) (n := ∞))
    (g : M → E → E → ℝ)
    (hOrtho : ∀ i : atlas H M, ∀ x,
      x ∈ (tangentBundleCore I M).baseSet i → ∀ v w : E,
      g x
        ((tangentBundleCore I M).coordChange i
          ((tangentBundleCore I M).indexAt x) x (F.fromFrame i x v))
        ((tangentBundleCore I M).coordChange i
          ((tangentBundleCore I M).indexAt x) x (F.fromFrame i x w)) =
        inner ℝ v w)
    (x : M) (v w : E) :
    g x v w =
      inner ℝ
        (F.toFrame ((tangentBundleCore I M).indexAt x) x v)
        (F.toFrame ((tangentBundleCore I M).indexAt x) x w) := by
  let C := tangentBundleCore I M
  let k := C.indexAt x
  have hk : x ∈ C.baseSet k := C.mem_baseSet_at x
  have h := hOrtho k x hk (F.toFrame k x v) (F.toFrame k x w)
  rw [C.coordChange_self k x hk, C.coordChange_self k x hk] at h
  rw [F.from_to k x hk, F.from_to k x hk] at h
  exact h

end
end QuaternionicSymmetry.ManifoldTangentFrameMetricIdentification
