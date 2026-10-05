import QuaternionicSymmetry.ManifoldQuaternionicFullSphereChartComparison
import QuaternionicSymmetry.ManifoldSphereAmbientNormalization

/-! The smooth full-isometry ambient extension can be radially projected
back to the actual sphere near each quaternionic isometry. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereNormalizedSmooth

open Manifold
open ManifoldQuaternionicFullSphereAmbientSmooth
open ManifoldQuaternionicFullSphereChartComparison
open ManifoldSphereAmbientNormalization
open ManifoldQuaternionicRiemannianDistance
open ManifoldTwistorCoefficientSphere
open MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def fullNormalizedSphereAction
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M) (uTarget : geometricSphere)
    (p : ((letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) × M) ×
      geometricSphere) : geometricSphere :=
  radialSphere uTarget (fullMovingSphereAmbient Q hChart hManifold g₀ x₀ p)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem contMDiffAt_fullNormalizedSphereAction
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hLie :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M) (uSource uTarget : geometricSphere)
    (hnonzero : fullMovingSphereAmbient Q hChart hManifold g₀ x₀
      ((g₀,x₀),uSource) ≠ 0) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2)) (𝓡 2) ∞
      (fullNormalizedSphereAction Q hChart hManifold g₀ x₀ uTarget)
      ((g₀,x₀),uSource) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  exact contMDiffAt_radialSphere
    (F := (V × E) × EuclideanSpace ℝ (Fin 2))
    (I := (𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2)) uTarget
    (contMDiffAt_fullMovingSphereAmbient Q hChart hManifold hLie hAction
      g₀ x₀ uSource) hnonzero

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereNormalizedSmooth
