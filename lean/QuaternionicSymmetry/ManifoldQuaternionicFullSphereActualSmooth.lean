import QuaternionicSymmetry.ManifoldQuaternionicFullSphereNormalizedComparison

/-! At every genuine quaternionic isometry and twistor point, the
full-isometry radial extension is smooth without any nonvanishing premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereActualSmooth

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereNormalizedSmooth
open ManifoldQuaternionicFullSphereChartComparison
open ManifoldQuaternionicFullSphereAmbientSmooth
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicRiemannianDistance
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
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

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem contMDiffAt_fullNormalizedSphereAction_at_actual
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
    (f₀ : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2)) (𝓡 2) ∞
      (fullNormalizedSphereAction Q hChart hManifold
        (toFullMetricIsometry Q f₀) z₀.1
        ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
          (sphereTotalMap Q f₀ z₀)).2)
      ((toFullMetricIsometry Q f₀,z₀.1),
        ((sphereCore Q).localTriv (achart E z₀.1) z₀).2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  let uTarget := ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
    (sphereTotalMap Q f₀ z₀)).2
  have hvalue := fullMovingSphereAmbient_eq_actual_chart Q hChart hManifold
    hAction f₀ f₀ z₀.1 z₀
    (mem_chart_source V (toFullMetricIsometry Q f₀))
    (by simpa using (mem_chart_source V (toFullMetricIsometry Q f₀)⁻¹))
    (mem_chart_source E z₀.1)
    (mem_chart_source E (f₀ • z₀.1))
  have hnonzero : fullMovingSphereAmbient Q hChart hManifold
      (toFullMetricIsometry Q f₀) z₀.1
      ((toFullMetricIsometry Q f₀,z₀.1),
        ((sphereCore Q).localTriv (achart E z₀.1) z₀).2) ≠ 0 := by
    rw [hvalue]
    exact ne_zero_of_mem_unit_sphere uTarget
  exact contMDiffAt_fullNormalizedSphereAction Q hChart hManifold hLie hAction
    (toFullMetricIsometry Q f₀) z₀.1
    ((sphereCore Q).localTriv (achart E z₀.1) z₀).2 uTarget hnonzero

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereActualSmooth
