import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! A source-free tangent-core calculation: if every local frame is
orthonormal for one pointwise metric after conversion to the preferred
tangent chart, then the actual adapted-core transition is orthogonal.
The projector model supplies this hypothesis separately by calculation. -/

namespace QuaternionicSymmetry.ManifoldTangentFrameMetricOverlap

open ManifoldQuaternionicReduction
open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [IsManifold I (∞ + 1) M]

theorem transition_inner_of_preferred_orthonormal
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
    (i j : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (hj : x ∈ (tangentBundleCore I M).baseSet j)
    (v w : E) :
    inner ℝ (F.coordChange i j x v) (F.coordChange i j x w) = inner ℝ v w := by
  let C := tangentBundleCore I M
  let k := C.indexAt x
  have hk : x ∈ C.baseSet k := C.mem_baseSet_at x
  have hToPref (z : E) :
      C.coordChange j k x (F.fromFrame j x (F.coordChange i j x z)) =
        C.coordChange i k x (F.fromFrame i x z) := by
    rw [F.coordChange_apply, F.from_to j x hj]
    exact C.coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩ _
  calc
    inner ℝ (F.coordChange i j x v) (F.coordChange i j x w) =
        g x
          (C.coordChange j k x (F.fromFrame j x (F.coordChange i j x v)))
          (C.coordChange j k x (F.fromFrame j x (F.coordChange i j x w))) :=
      (hOrtho j x hj _ _).symm
    _ = g x (C.coordChange i k x (F.fromFrame i x v))
        (C.coordChange i k x (F.fromFrame i x w)) := by rw [hToPref, hToPref]
    _ = inner ℝ v w := hOrtho i x hi v w

end
end QuaternionicSymmetry.ManifoldTangentFrameMetricOverlap
