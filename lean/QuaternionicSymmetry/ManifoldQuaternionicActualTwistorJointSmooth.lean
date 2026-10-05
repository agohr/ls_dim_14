import QuaternionicSymmetry.ManifoldQuaternionicActualTangentNeighborhood
import QuaternionicSymmetry.ManifoldQuaternionicFullSphereLocalTangent

/-! BG-R3 alone yields the genuine jointly continuous real tangent action
of the quaternionic-isometry twistor lift. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualTwistorJointSmooth

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicActualTangentNeighborhood
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldQuaternionicFullSphereJointChartComparison
open ManifoldQuaternionicFullSphereLocalTangent
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicSphereChartSmooth
open ManifoldTangentMapContinuousAt
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

theorem joint_smooth
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [ChartedSpace W (QuaternionicIsometries Q)]
    [IsManifold 𝓘(ℝ,W) ∞ (QuaternionicIsometries Q)]
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
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hi :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff 𝓘(ℝ,W) 𝓘(ℝ,V) ∞ (toFullMetricIsometry Q)) :
    ContMDiff (𝓘(ℝ,W).prod (J (E := E))) (J (E := E)) ∞
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q => sphereTotalMap Q p.1 p.2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  intro p₀
  let f₀ := p₀.1
  let z₀ := p₀.2
  let w₀ := sphereTotalMap Q f₀ z₀
  let C := chartAt (M × geometricSphere) z₀
  let D := chartAt (M × geometricSphere) w₀
  let L : (M ≃ᵢ M) × (M × geometricSphere) → M × geometricSphere :=
    fullSphereJointLocalAction Q hChart hManifold
      (toFullMetricIsometry Q f₀) z₀.1
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1)) w₀).2
  have hinput : ContMDiffAt (𝓘(ℝ,W).prod (J (E := E)))
      (𝓘(ℝ,V).prod (J (E := E))) ∞
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        (toFullMetricIsometry Q p.1,C p.2)) p₀ :=
    (hi.contMDiffAt.comp p₀ contMDiffAt_fst).prodMk
      ((preferredLocalTriv_smoothAt Q z₀).comp p₀ contMDiffAt_snd)
  have hL : ContMDiffAt (𝓘(ℝ,V).prod (J (E := E))) (J (E := E)) ∞ L
      (toFullMetricIsometry Q f₀,C z₀) :=
    contMDiffAt_fullSphereJointLocalAction_at_actual Q hChart hManifold hLie hAction f₀ z₀
  have hcenter : L (toFullMetricIsometry Q f₀,C z₀) = D w₀ :=
    fullSphereJointLocalAction_eq_chart Q hChart hManifold hAction
      f₀ f₀ z₀.1 z₀
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1)) w₀).2
      (mem_chart_source V (toFullMetricIsometry Q f₀))
      (by simpa using (mem_chart_source V (toFullMetricIsometry Q f₀)⁻¹))
      (mem_chart_source E z₀.1) (mem_chart_source E (f₀ • z₀.1))
  have hD : ContMDiffAt (J (E := E)) (J (E := E)) ∞ D.symm
      (L (toFullMetricIsometry Q f₀,C z₀)) := by
    rw [hcenter]
    exact preferredLocalTriv_symm_smoothAt Q w₀
  have hRHS := hD.comp p₀ (hL.comp p₀ hinput)
  let zero : SphereBundleTotal Q → TangentBundle (J (E := E)) (SphereBundleTotal Q) :=
    fun z => ⟨z,0⟩
  have hzero : Continuous zero :=
    (Bundle.mdifferentiable_zeroSection (IB := J (E := E)) ℝ (TangentSpace (J (E := E)))).continuous
  have ht := (continuous_fst.prodMk (hzero.comp continuous_snd)).continuousAt
      (x := p₀)
  have hevent := ht.tendsto.eventually
    (eventually_actual_tangentMap_fixedCharts Q hChart hManifold hLie hAction hR3 f₀ (zero z₀))
  apply hRHS.congr_of_eventuallyEq
  filter_upwards [hevent] with p hp
  exact congrArg (fun v : TangentBundle (J (E := E)) (SphereBundleTotal Q) => v.1) hp

end
end QuaternionicSymmetry.ManifoldQuaternionicActualTwistorJointSmooth
