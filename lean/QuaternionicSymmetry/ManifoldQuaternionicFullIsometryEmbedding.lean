import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! Embed the actual quaternionic-preserving smooth isometry group into
the full distance-isometry group with its proved compact-open topology.
This does not claim the quaternionic subgroup is closed or compact. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicMetricIsometryDistance
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Genuine quaternionic-preserving smooth isometries, viewed as actual
distance isometries of the Riemannian path metric. -/
def toFullMetricIsometry : QuaternionicIsometries Q →*
    (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) where
  toFun f := metricIsometryEquiv Q f.1 f.2.1
  map_one' := by
    letI : MetricSpace M := riemannianMetricSpace Q
    apply IsometryEquiv.ext
    intro x
    rfl
  map_mul' f g := by
    letI : MetricSpace M := riemannianMetricSpace Q
    apply IsometryEquiv.ext
    intro x
    rfl

theorem toFullMetricIsometry_injective :
    Function.Injective (toFullMetricIsometry Q) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  exact congrFun (congrArg (fun e :
    (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) =>
      (e : M → M)) h) x

theorem toFullMetricIsometry_pair (f : QuaternionicIsometries Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    isometryEquivToContinuousPairs (X := M) (toFullMetricIsometry Q f) =
      mapPair Q f := by
  letI : MetricSpace M := riemannianMetricSpace Q
  ext x <;> rfl

/-- The genuine quaternionic-isometry compact-open topology is the
subspace topology inherited from the full metric-isometry group. -/
theorem toFullMetricIsometry_continuous :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Continuous (toFullMetricIsometry Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  rw [isometryEquivTopology_eq_compactOpen]
  apply continuous_induced_rng.mpr
  have hp : Continuous (mapPair Q) := continuous_mapPair Q
  simpa only [Function.comp_def, toFullMetricIsometry_pair] using hp

theorem subgroup_toFullMetricIsometry_continuous
    (S : Subgroup (QuaternionicIsometries Q)) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Continuous (fun f : S => toFullMetricIsometry Q f.1) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  exact (toFullMetricIsometry_continuous Q).comp continuous_subtype_val

end
end QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding
