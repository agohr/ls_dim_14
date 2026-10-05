import QuaternionicSymmetry.ManifoldQuaternionicFullSphereLocalTangent
import QuaternionicSymmetry.ManifoldQuaternionicFullSphereNormalizedComparison

/-! The full-group smooth local action equals the fixed-chart expression
of the genuine quaternionic twistor lift throughout the overlap. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointChartComparison

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldQuaternionicFullSphereNormalizedComparison
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

theorem fullSphereJointLocalAction_eq_chart
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
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (f₀ f : QuaternionicIsometries Q) (x₀ : M) (z : SphereBundleTotal Q)
    (uTarget : geometricSphere)
    (hg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      toFullMetricIsometry Q f ∈
        (chartAt V (toFullMetricIsometry Q f₀)).source)
    (hgi :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      (toFullMetricIsometry Q f)⁻¹ ∈
        (chartAt V (toFullMetricIsometry Q f₀)⁻¹).source)
    (hx : z.1 ∈ (chartAt E x₀).source)
    (hy : f • z.1 ∈ (chartAt E (f₀ • x₀)).source) :
    fullSphereJointLocalAction Q hChart hManifold
      (toFullMetricIsometry Q f₀) x₀ uTarget
      (toFullMetricIsometry Q f,
        ((sphereCore Q).localTriv (achart E x₀) z)) =
      (sphereCore Q).localTriv (achart E (f₀ • x₀))
        (sphereTotalMap Q f z) := by
  apply Prod.ext
  · exact (sphereTotalMap_base Q f z).symm
  · exact fullNormalizedSphereAction_eq_actual_chart Q hChart hManifold
      hAction f₀ f x₀ z uTarget hg hgi hx hy

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointChartComparison
