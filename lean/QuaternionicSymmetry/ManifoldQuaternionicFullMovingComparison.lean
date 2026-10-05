import QuaternionicSymmetry.ManifoldQuaternionicFullMovingCoefficientSmooth
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereCoordinate

/-! Comparison of the full-isometry smooth derivative extension with the
actual quaternionic derivative in two fixed adapted charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullMovingComparison

open Manifold
open ManifoldQuaternionicFullMovingAdaptedSmooth
open ManifoldQuaternionicFullMovingCoefficientSmooth
open ManifoldQuaternionicJointMovingDerivative
open ManifoldQuaternionicJointMovingAdaptedDerivative
open ManifoldQuaternionicJointSphereCoordinate
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicSpanSymmetry
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

theorem fullMovingAdaptedDerivative_eq_actual
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
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M)
    (hg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      toFullMetricIsometry Q f ∈
        (chartAt V (toFullMetricIsometry Q f₀)).source)
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source) :
    fullMovingAdaptedDerivative Q hChart hManifold
      (toFullMetricIsometry Q f₀) x₀ (toFullMetricIsometry Q f,x) =
      movingAdaptedDerivative Q f₀ x₀ (f,x) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  have hpart := jointPartial_eq_individualMovingCharts Q hChart hManifold
    hAction (toFullMetricIsometry Q f₀) (toFullMetricIsometry Q f)
    x₀ x hg hx (by simpa using hy)
  have hcong := congrArg (fun D : E →L[ℝ] E =>
    (Q.frames.toFrame (achart E (f₀ • x₀)) (f • x)).comp
      (D.comp (Q.frames.fromFrame (achart E x₀) x))) hpart
  exact hcong

theorem fullMovingInverseDerivative_eq_actual
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
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M)
    (hg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      (toFullMetricIsometry Q f)⁻¹ ∈
        (chartAt V (toFullMetricIsometry Q f₀)⁻¹).source)
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source) :
    fullMovingInverseDerivative Q hChart hManifold
      (toFullMetricIsometry Q f₀) x₀ (toFullMetricIsometry Q f,x) =
      movingAdaptedInverseDerivative Q f₀ x₀ (f,x) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  have h := fullMovingAdaptedDerivative_eq_actual Q hChart hManifold hAction
    f₀⁻¹ f⁻¹ (f₀ • x₀) (f • x) (by simpa using hg) hy (by simpa using hx)
  simpa only [fullMovingInverseDerivative, movingAdaptedInverseDerivative,
    map_inv, inv_smul_smul] using h

theorem fullMovingCoefficientRotation_eq_true
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
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M) (a : Fin 3 → ℝ)
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
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source) :
    fullMovingCoefficientRotation Q hChart hManifold
      (toFullMetricIsometry Q f₀) x₀
      ((toFullMetricIsometry Q f,x),a) =
      movingTrueCoefficientAction Q f₀ x₀ a (f,x) := by
  rw [fullMovingCoefficientRotation,
    fullMovingAdaptedDerivative_eq_actual Q hChart hManifold hAction
      f₀ f x₀ x hg hx hy,
    fullMovingInverseDerivative_eq_actual Q hChart hManifold hAction
      f₀ f x₀ x hgi hx hy]
  exact movingCoefficientRotation_eq_true_on_overlap Q f₀ f x₀ x hx hy a

end
end QuaternionicSymmetry.ManifoldQuaternionicFullMovingComparison
