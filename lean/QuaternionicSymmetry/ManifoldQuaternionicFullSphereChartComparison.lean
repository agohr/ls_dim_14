import QuaternionicSymmetry.ManifoldQuaternionicFullSphereAmbientSmooth
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereBundleBridge

/-! On the fixed-chart overlap, the smooth ambient full-isometry
formula is precisely the actual quaternionic twistor-lift sphere coordinate. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereChartComparison

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereAmbientSmooth
open ManifoldQuaternionicFullMovingComparison
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicJointSphereBundleBridge
open ManifoldQuaternionicJointSphereCoordinate
open ManifoldQuaternionicTwistorLocalAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicRiemannianDistance
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
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

theorem fullMovingSphereAmbient_eq_actual_chart
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
    fullMovingSphereAmbient Q hChart hManifold
      (toFullMetricIsometry Q f₀) x₀
      ((toFullMetricIsometry Q f,z.1),((sphereCore Q).localTriv (achart E x₀) z).2) =
      (((sphereCore Q).localTriv (achart E (f₀ • x₀))
        (sphereTotalMap Q f z)).2 : EuclideanThree) := by
  let i := achart E x₀
  let j := achart E (f₀ • x₀)
  have hcoeff := fullMovingCoefficientRotation_eq_true Q hChart hManifold
    hAction f₀ f x₀ z.1 (sphereChartCoefficient Q i z) hg hgi hx hy
  have hsource : sphereChartCoefficient Q i z =
      EuclideanSpace.equiv (Fin 3) ℝ
        (((sphereCore Q).localTriv i z).2 : EuclideanThree) := rfl
  have htarget : sphereChartCoefficient Q j (sphereTotalMap Q f z) =
      EuclideanSpace.equiv (Fin 3) ℝ
        ((((sphereCore Q).localTriv j (sphereTotalMap Q f z)).2) : EuclideanThree) := rfl
  have hactual := sphereChartCoefficient_movingLift Q f₀ f x₀ z hx hy
  have hmove := movingCoefficientRotation_eq_true_on_overlap Q f₀ f x₀ z.1
    hx hy (sphereChartCoefficient Q i z)
  rw [hsource] at hcoeff hactual
  rw [htarget] at hactual
  rw [hsource] at hmove
  have h := congrArg toEuclidean (hcoeff.trans (hmove.symm.trans hactual.symm))
  simpa only [fullMovingSphereAmbient, toEuclidean,
    LinearEquiv.symm_apply_apply] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereChartComparison
