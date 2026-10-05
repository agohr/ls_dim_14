import QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointChartComparison
import QuaternionicSymmetry.ManifoldTangentMapLocalConjugation
import QuaternionicSymmetry.ManifoldQuaternionicSphereChartSmooth

/-! Exact tangent-map conjugation by fixed real sphere-bundle charts,
on the overlap where the full-Lie-group local action is differentiable. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualTangentConjugation

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldQuaternionicFullSphereJointChartComparison
open ManifoldTangentMapLocalConjugation
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
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance
private abbrev J := 𝓘(ℝ,E).prod (𝓡 2)

theorem actual_tangentMap_fixedCharts
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
    (f₀ f : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q)
    (v : TangentBundle (J (E := E)) (SphereBundleTotal Q))
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
    (hx : v.1.1 ∈ (chartAt E z₀.1).source)
    (hy : f • v.1.1 ∈ (chartAt E (f₀ • z₀.1)).source)
    (hlocal : MDifferentiableAt (J (E := E)) (J (E := E))
      (fun q : M × geometricSphere =>
        fullSphereJointLocalAction Q hChart hManifold
          (toFullMetricIsometry Q f₀) z₀.1
          ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
            (sphereTotalMap Q f₀ z₀)).2
          (toFullMetricIsometry Q f,q))
      ((sphereCore Q).localTriv (achart E z₀.1) v.1))
    (hC : MDifferentiableAt (J (E := E)) (J (E := E))
      (chartAt (M × geometricSphere) z₀) v.1)
    (hD : MDifferentiableAt (J (E := E)) (J (E := E))
      (chartAt (M × geometricSphere) (sphereTotalMap Q f₀ z₀)).symm
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
        (sphereTotalMap Q f v.1))) :
    tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q f) v =
      tangentMap (J (E := E)) (J (E := E))
        (chartAt (M × geometricSphere) (sphereTotalMap Q f₀ z₀)).symm
        (tangentMap (J (E := E)) (J (E := E))
          (fun q : M × geometricSphere =>
            fullSphereJointLocalAction Q hChart hManifold
              (toFullMetricIsometry Q f₀) z₀.1
              ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
                (sphereTotalMap Q f₀ z₀)).2
              (toFullMetricIsometry Q f,q))
          (tangentMap (J (E := E)) (J (E := E))
            (chartAt (M × geometricSphere) z₀) v)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let C := chartAt (M × geometricSphere) z₀
  let D := chartAt (M × geometricSphere) (sphereTotalMap Q f₀ z₀)
  let L : M × geometricSphere → M × geometricSphere := fun q =>
    fullSphereJointLocalAction Q hChart hManifold
      (toFullMetricIsometry Q f₀) z₀.1
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
        (sphereTotalMap Q f₀ z₀)).2
      (toFullMetricIsometry Q f,q)
  have hCmem : v.1 ∈ C.source :=
    ((sphereCore Q).mem_localTriv_source (achart E z₀.1) v.1).2 hx
  have hDmem : sphereTotalMap Q f v.1 ∈ D.source :=
    ((sphereCore Q).mem_localTriv_source (achart E (f₀ • z₀.1))
      (sphereTotalMap Q f v.1)).2
      (by simpa only [sphereTotalMap_base] using hy)
  have hD' : MDifferentiableAt (J (E := E)) (J (E := E)) D.symm (L (C v.1)) := by
    have hvalue : L (C v.1) = D (sphereTotalMap Q f v.1) :=
      fullSphereJointLocalAction_eq_chart Q hChart hManifold hAction
        f₀ f z₀.1 v.1 _ hg hgi hx hy
    rw [hvalue]
    exact hD
  have hsource : ∀ᶠ y : SphereBundleTotal Q in nhds v.1,
      y.1 ∈ (chartAt E z₀.1).source :=
    ((chartAt E z₀.1).open_source.preimage (sphereCore Q).continuous_proj).mem_nhds hx
  have htarget : ∀ᶠ y : SphereBundleTotal Q in nhds v.1,
      f • y.1 ∈ (chartAt E (f₀ • z₀.1)).source := by
    have hbase : Continuous (fun y : SphereBundleTotal Q => f • y.1) :=
      f.1.contMDiff.continuous.comp (sphereCore Q).continuous_proj
    exact ((chartAt E (f₀ • z₀.1)).open_source.preimage hbase).mem_nhds hy
  have heq : (sphereTotalMap Q f) =ᶠ[nhds v.1] D.symm ∘ L ∘ C := by
    filter_upwards [hsource, htarget] with y hxy hyy
    have hvalue := fullSphereJointLocalAction_eq_chart Q hChart hManifold hAction
      f₀ f z₀.1 y
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
        (sphereTotalMap Q f₀ z₀)).2 hg hgi hxy hyy
    change L (C y) = D (sphereTotalMap Q f y) at hvalue
    have hDsource : sphereTotalMap Q f y ∈ D.source :=
      ((sphereCore Q).mem_localTriv_source (achart E (f₀ • z₀.1))
        (sphereTotalMap Q f y)).2
        (by simpa only [sphereTotalMap_base] using hyy)
    change sphereTotalMap Q f y = D.symm (L (C y))
    rw [hvalue]
    exact (D.left_inv hDsource).symm
  exact tangentMap_eq_of_eventually_conjugate v heq hC hlocal hD'

end
end QuaternionicSymmetry.ManifoldQuaternionicActualTangentConjugation
