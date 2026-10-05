import QuaternionicSymmetry.ManifoldQuaternionicActualTangentConjugation
import QuaternionicSymmetry.ManifoldJointSpatialSliceDifferentiability
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity

/-! Near any actual isometry and twistor tangent, the exact fixed-chart
tangent conjugation holds throughout a neighborhood. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualTangentNeighborhood

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicActualTangentConjugation
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicJointSphereContinuity
open ManifoldQuaternionicSphereChartSmooth
open ManifoldJointSpatialSliceDifferentiability
open ManifoldLocalC1Neighborhood
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

theorem eventually_actual_tangentMap_fixedCharts
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
    ∀ᶠ p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      tangentMap (J (E := E)) (J (E := E))
        (sphereTotalMap Q p.1) p.2 =
      tangentMap (J (E := E)) (J (E := E))
        (chartAt (M × geometricSphere) (sphereTotalMap Q f₀ v₀.1)).symm
        (tangentMap (J (E := E)) (J (E := E))
          (fun q : M × geometricSphere =>
            letI : MetricSpace M := riemannianMetricSpace Q
            letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
            fullSphereJointLocalAction Q hChart hManifold
              (toFullMetricIsometry Q f₀) v₀.1.1
              ((sphereCore Q).localTriv (achart E (f₀ • v₀.1.1))
                (sphereTotalMap Q f₀ v₀.1)).2
              (toFullMetricIsometry Q p.1,q))
          (tangentMap (J (E := E)) (J (E := E))
            (chartAt (M × geometricSphere) v₀.1) p.2)) := by
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
  have hproj : Continuous (fun v : TangentBundle (J (E := E))
      (SphereBundleTotal Q) => v.1) :=
    FiberBundle.continuous_proj (E × EuclideanSpace ℝ (Fin 2))
      (TangentSpace (J (E := E)))
  have hCsmooth : ContMDiffAt (J (E := E)) (J (E := E)) ∞ C z₀ :=
    preferredLocalTriv_smoothAt Q z₀
  have hDsmooth : ContMDiffAt (J (E := E)) (J (E := E)) ∞ D.symm (D w₀) :=
    preferredLocalTriv_symm_smoothAt Q w₀
  have hCnear : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      MDifferentiableAt (J (E := E)) (J (E := E)) C p.2.1 := by
    have hbase : ContinuousAt (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => p.2.1) (f₀,v₀) :=
      (hproj.comp continuous_snd).continuousAt
    exact hbase.tendsto.eventually
      (eventually_mdifferentiableAt_of_contMDiffAt hCsmooth)
  have hCcont : ContinuousAt C z₀ := hCsmooth.continuousAt
  have hinput : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
        (toFullMetricIsometry Q p.1,C p.2.1)) (f₀,v₀) := by
    have hg := (toFullMetricIsometry_continuous Q).continuousAt.comp
      (f := Prod.fst) (x := (f₀,v₀)) continuousAt_fst
    have hz := hCcont.comp (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => p.2.1)
      (x := (f₀,v₀)) (hproj.comp continuous_snd).continuousAt
    exact hg.prodMk hz
  have hLsmooth : ContMDiffAt (𝓘(ℝ,V).prod (J (E := E)))
      (J (E := E)) ∞ L (toFullMetricIsometry Q f₀,C z₀) :=
    contMDiffAt_fullSphereJointLocalAction_at_actual Q hChart
      hManifold hLie hAction f₀ z₀
  have hLnear : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      MDifferentiableAt (J (E := E)) (J (E := E))
        (fun q : M × geometricSphere => L (toFullMetricIsometry Q p.1,q))
        (C p.2.1) :=
    eventually_mdifferentiableAt_spatial_slices hLsmooth
      ((toFullMetricIsometry_continuous Q).continuousAt.comp
        (f := Prod.fst) (x := (f₀,v₀)) continuousAt_fst)
      (hCcont.comp (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => p.2.1)
        (x := (f₀,v₀)) (hproj.comp continuous_snd).continuousAt)
      rfl rfl
  have hwcont : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      sphereTotalMap Q p.1 p.2.1) (f₀,v₀) := by
    have hbase : Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => (p.1,p.2.1)) :=
      continuous_fst.prodMk (hproj.comp continuous_snd)
    exact (continuous_jointSphereTotalMap Q hR3).continuousAt.comp
      (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => (p.1,p.2.1))
      (x := (f₀,v₀)) hbase.continuousAt
  have hDcoord : ContinuousAt (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      D (sphereTotalMap Q p.1 p.2.1)) (f₀,v₀) :=
    (preferredLocalTriv_smoothAt Q w₀).continuousAt.comp
      (f := fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
          sphereTotalMap Q p.1 p.2.1) (x := (f₀,v₀)) hwcont
  have hDnear : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      MDifferentiableAt (J (E := E)) (J (E := E)) D.symm
        (D (sphereTotalMap Q p.1 p.2.1)) :=
    hDcoord.tendsto.eventually
      (eventually_mdifferentiableAt_of_contMDiffAt hDsmooth)
  have hg : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      toFullMetricIsometry Q p.1 ∈
        (chartAt V (toFullMetricIsometry Q f₀)).source :=
    ((chartAt V (toFullMetricIsometry Q f₀)).open_source.preimage
      ((toFullMetricIsometry_continuous Q).comp continuous_fst)).mem_nhds
      (mem_chart_source V (toFullMetricIsometry Q f₀))
  have hgi : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      (toFullMetricIsometry Q p.1)⁻¹ ∈
        (chartAt V (toFullMetricIsometry Q f₀)⁻¹).source := by
    have hmap : Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
        (toFullMetricIsometry Q p.1)⁻¹) :=
      (contMDiff_inv 𝓘(ℝ,V) ∞).continuous.comp
        ((toFullMetricIsometry_continuous Q).comp continuous_fst)
    exact ((chartAt V (toFullMetricIsometry Q f₀)⁻¹).open_source.preimage hmap).mem_nhds
      (mem_chart_source V (toFullMetricIsometry Q f₀)⁻¹)
  have hx : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      p.2.1.1 ∈ (chartAt E z₀.1).source := by
    have hbase : Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) => p.2.1.1) :=
      (sphereCore Q).continuous_proj.comp (hproj.comp continuous_snd)
    exact ((chartAt E z₀.1).open_source.preimage hbase).mem_nhds
      (mem_chart_source E z₀.1)
  have hy : ∀ᶠ p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
      p.1 • p.2.1.1 ∈ (chartAt E (f₀ • z₀.1)).source := by
    have hbase : Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
        (sphereTotalMap Q p.1 p.2.1).1) :=
      (sphereCore Q).continuous_proj.comp
        ((continuous_jointSphereTotalMap Q hR3).comp
          (continuous_fst.prodMk (hproj.comp continuous_snd)))
    have htargetEvent : ∀ᶠ p : QuaternionicIsometries Q ×
        TangentBundle (J (E := E)) (SphereBundleTotal Q) in nhds (f₀,v₀),
        (sphereTotalMap Q p.1 p.2.1).1 ∈
          (chartAt E (f₀ • z₀.1)).source :=
      ((chartAt E (f₀ • z₀.1)).open_source.preimage hbase).mem_nhds
        (by simpa only [Set.mem_preimage, sphereTotalMap_base] using
          (mem_chart_source E (f₀ • z₀.1)))
    filter_upwards [htargetEvent] with p hp
    simpa only [sphereTotalMap_base] using hp
  filter_upwards [hg,hgi,hx,hy,hLnear,hCnear,hDnear] with p hgp hgip hxp hyp hLp hCp hDp
  exact actual_tangentMap_fixedCharts Q hChart hManifold hAction f₀ p.1 z₀ p.2
    hgp hgip hxp hyp hLp hCp hDp

end
end QuaternionicSymmetry.ManifoldQuaternionicActualTangentNeighborhood
