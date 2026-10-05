import QuaternionicSymmetry.MetricIsometryCompactness
import QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryDistance

/-! Compactness of the full metric-isometry group for the genuine path
metric of a compact connected quaternionic Riemannian manifold. This does
not identify the smooth quaternionic-preserving subgroup as a closed Lie
subgroup, nor its Lie algebra with Killing fields. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryCompact
open ManifoldQuaternionicRiemannianDistance
open QuaternionicSymmetry.MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The self-isometries of the actual Riemannian path metric are compact
for uniform convergence of both the map and its inverse. -/
theorem actualMetricIsometry_compactSpace :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    CompactSpace (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  exact isometryEquiv_compactSpace (X := M)

/-- The full isometry group of the genuine path metric is a compact
topological group, with the compact-open topology on an isometry and its
inverse. No quaternionic-preservation condition is imposed here. -/
theorem actualMetricIsometry_topologicalGroup :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    IsTopologicalGroup (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  exact isometryEquiv_topologicalGroup (X := M)

theorem actualMetricIsometry_action_continuous :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Continuous (fun p : (M ≃ᵢ M) × M => p.1 p.2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  exact isometryEquiv_action_continuous (X := M)

end
end QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryCompact
