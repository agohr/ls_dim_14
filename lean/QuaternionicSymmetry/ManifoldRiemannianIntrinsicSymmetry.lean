import QuaternionicSymmetry.ManifoldMetricHomothety

/-! Intrinsic Riemannian symmetry of an actual smooth metric.  A point
symmetry is a globally defined smooth metric isometry fixing its center,
with differential `-id` there.  The definition contains neither a model
name nor a classification conclusion. -/

namespace QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

open ManifoldMetricHomothety ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A genuine global smooth point isometry with differential `-id`. -/
structure PointSymmetry
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (x : M) where
  map : MetricHomothety Q Q
  scale_one : map.scale = 1
  fixed : map.map x = x
  deriv_neg : ∀ v : TangentSpace 𝓘(ℝ,E) x,
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (map.map : M → M) x v = -v

/-- At each point the metric admits an actual globally defined geodesic
point symmetry, expressed by its characteristic differential. -/
def IsRiemannianSymmetric
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) :
    Prop := ∀ x : M, Nonempty (PointSymmetry Q x)

theorem PointSymmetry.metric_invariant
    {Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞)}
    {x : M} (s : PointSymmetry Q x) (y : M)
    (v w : TangentSpace 𝓘(ℝ,E) y) :
    Q.tangentMetricForm (s.map.map y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (s.map.map : M → M) y v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (s.map.map : M → M) y w) =
      Q.tangentMetricForm y v w := by
  simpa [s.scale_one] using s.map.metric_eq y v w

end
end QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
