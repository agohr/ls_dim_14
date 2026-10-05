import QuaternionicSymmetry.ManifoldQuaternionicActualTangentNeighborhood
import QuaternionicSymmetry.ManifoldQuaternionicFullSphereLocalTangent

/-! BG-R3 alone yields the genuine jointly continuous real tangent action
of the quaternionic-isometry twistor lift. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualTwistorTangentContinuity

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

theorem continuousAt_actual_twistorTangentAction
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
    (f₀ : QuaternionicIsometries Q)
    (v₀ : TangentBundle (J (E := E)) (SphereBundleTotal Q)) :
    ContinuousAt (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E))
        (sphereTotalMap Q p.1) p.2) (f₀,v₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  let z₀ := v₀.1
  let w₀ := sphereTotalMap Q f₀ z₀
  let C := chartAt (M × geometricSphere) z₀
  let D := chartAt (M × geometricSphere) w₀
  let L : (M ≃ᵢ M) × (M × geometricSphere) → M × geometricSphere :=
    fullSphereJointLocalAction Q hChart hManifold
      (toFullMetricIsometry Q f₀) z₀.1
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1)) w₀).2
  have hCsmooth : ContMDiffAt (J (E := E)) (J (E := E)) ∞ C z₀ :=
    preferredLocalTriv_smoothAt Q z₀
  have hCcont : ContinuousAt (tangentMap (J (E := E)) (J (E := E)) C) v₀ :=
    continuousAt_tangentMap_of_contMDiffAt (hCsmooth.of_le (by simp))
  have hinput : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      (toFullMetricIsometry Q p.1,
        tangentMap (J (E := E)) (J (E := E)) C p.2)) (f₀,v₀) := by
    have hg : ContinuousAt (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
        toFullMetricIsometry Q p.1) (f₀,v₀) :=
      ((toFullMetricIsometry_continuous Q).comp continuous_fst).continuousAt
    exact hg.prodMk (hCcont.comp (f := Prod.snd) (x := (f₀,v₀)) continuousAt_snd)
  have hCbase : (tangentMap (J (E := E)) (J (E := E)) C v₀).1 =
      (z₀.1,((sphereCore Q).localTriv (achart E z₀.1) z₀).2) := rfl
  have hLocal : ContinuousAt (fun p : (M ≃ᵢ M) ×
      TangentBundle (J (E := E)) (M × geometricSphere) =>
      tangentMap (J (E := E)) (J (E := E))
        (fun q => L (p.1,q)) p.2)
      (toFullMetricIsometry Q f₀,
        tangentMap (J (E := E)) (J (E := E)) C v₀) :=
    continuousAt_fullSphereLocalSpatialTangent Q hChart hManifold hLie hAction
      f₀ z₀ (tangentMap (J (E := E)) (J (E := E)) C v₀) hCbase
  have hMiddle : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E))
        (fun q => L (toFullMetricIsometry Q p.1,q))
        (tangentMap (J (E := E)) (J (E := E)) C p.2)) (f₀,v₀) :=
    ContinuousAt.comp
      (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
        (toFullMetricIsometry Q p.1,
          tangentMap (J (E := E)) (J (E := E)) C p.2))
      (g := fun p : (M ≃ᵢ M) ×
        TangentBundle (J (E := E)) (M × geometricSphere) =>
          tangentMap (J (E := E)) (J (E := E))
            (fun q => L (p.1,q)) p.2)
      hLocal hinput
  have hcenter : L (toFullMetricIsometry Q f₀,C z₀) = D w₀ :=
    fullSphereJointLocalAction_eq_chart Q hChart hManifold hAction
      f₀ f₀ z₀.1 z₀
      ((sphereCore Q).localTriv (achart E (f₀ • z₀.1)) w₀).2
      (mem_chart_source V (toFullMetricIsometry Q f₀))
      (by simpa using (mem_chart_source V (toFullMetricIsometry Q f₀)⁻¹))
      (mem_chart_source E z₀.1)
      (mem_chart_source E (f₀ • z₀.1))
  have hMiddleBase :
      (tangentMap (J (E := E)) (J (E := E))
        (fun q => L (toFullMetricIsometry Q f₀,q))
        (tangentMap (J (E := E)) (J (E := E)) C v₀)).1 = D w₀ := by
    change L (toFullMetricIsometry Q f₀,C z₀) = D w₀
    exact hcenter
  have hDsmooth : ContMDiffAt (J (E := E)) (J (E := E)) 1 D.symm
      (tangentMap (J (E := E)) (J (E := E))
        (fun q => L (toFullMetricIsometry Q f₀,q))
        (tangentMap (J (E := E)) (J (E := E)) C v₀)).1 := by
    rw [hMiddleBase]
    exact (preferredLocalTriv_symm_smoothAt Q w₀).of_le (by simp)
  have hDcont : ContinuousAt (tangentMap (J (E := E)) (J (E := E)) D.symm)
      (tangentMap (J (E := E)) (J (E := E))
        (fun q => L (toFullMetricIsometry Q f₀,q))
        (tangentMap (J (E := E)) (J (E := E)) C v₀)) :=
    continuousAt_tangentMap_of_contMDiffAt hDsmooth
  have hRHS : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) D.symm
        (tangentMap (J (E := E)) (J (E := E))
          (fun q => L (toFullMetricIsometry Q p.1,q))
          (tangentMap (J (E := E)) (J (E := E)) C p.2))) (f₀,v₀) :=
    ContinuousAt.comp
      (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
          tangentMap (J (E := E)) (J (E := E))
            (fun q => L (toFullMetricIsometry Q p.1,q))
            (tangentMap (J (E := E)) (J (E := E)) C p.2))
      (g := tangentMap (J (E := E)) (J (E := E)) D.symm)
      hDcont hMiddle
  have hevent := eventually_actual_tangentMap_fixedCharts Q hChart hManifold
    hLie hAction hR3 f₀ v₀
  exact hRHS.congr_of_eventuallyEq hevent

/-- Joint continuity of the actual twistor lift's tangent action in its
constructed real base–sphere atlas; no extra tangent regularity premise. -/
theorem continuous_jointSphereTangentAction
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E))
        (sphereTotalMap Q p.1) p.2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  apply continuous_iff_continuousAt.mpr
  intro p
  exact continuousAt_actual_twistorTangentAction Q hChart hManifold hLie
    hAction hR3 p.1 p.2

end
end QuaternionicSymmetry.ManifoldQuaternionicActualTwistorTangentContinuity
