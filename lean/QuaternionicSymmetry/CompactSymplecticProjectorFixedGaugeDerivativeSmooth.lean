import QuaternionicSymmetry.CompactSymplecticProjectorTangentChartChangeSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeSmooth

/-! Recenter the smooth action differential at an arbitrary point of a
fixed gauge chart by the actual smooth tangent-chart transition. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeDerivativeSmooth

open Manifold Filter Set
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalDerivativeSmooth
open CompactSymplecticProjectorLocalDerivativeCoordinateFormula
open CompactSymplecticProjectorTangentChartChangeSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem gaugeDerivativeCoordinates_smoothAt_of_overlap
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x y : ProjectiveCarrier n) (hy : y ∈ U) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    (∀ᶠ z in 𝓝 y,
      leftCosetAction n (σ z) (baseCoset n) ∈
        (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source ∩
          (chartAt (RModel q) (leftCosetAction n (σ y) (baseCoset n))).source) →
    ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (gaugeDerivativeCoordinates n d e q g a σ x) y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hxy hEv
  let C : ProjectiveCarrier n → RModel q →L[ℝ] RModel q :=
    tangentCoordChange 𝓘(ℝ, RModel q)
      (leftCosetAction n (σ y) (baseCoset n))
      (leftCosetAction n (σ x) (baseCoset n)) ∘
      (fun z => leftCosetAction n (σ z) (baseCoset n))
  have hC : ContMDiffAt 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞ C y := by
    have hmem :
        (chartAt (RModel q) (leftCosetAction n (σ y) (baseCoset n))).source ∩
          (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source ∈
        𝓝 (leftCosetAction n (σ y) (baseCoset n)) :=
      ((chartAt (RModel q) (leftCosetAction n (σ y) (baseCoset n))).open_source.inter
        (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).open_source).mem_nhds
        ⟨mem_chart_source _ _, hxy⟩
    have hcy := (tangentCoordChange_smoothOn n d e q g a
      (leftCosetAction n (σ y) (baseCoset n))
      (leftCosetAction n (σ x) (baseCoset n))).contMDiffAt hmem
    have hOrbit : ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
        (fun z => leftCosetAction n (σ z) (baseCoset n)) y := by
      have hp := (hσ.contMDiffAt (hU.mem_nhds hy)).prodMk
        (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, RModel q)
          𝓘(ℝ, RModel q) ∞ (fun _ : ProjectiveCarrier n => baseCoset n) y)
      exact a.actionSmooth.contMDiffAt.comp y hp
    exact hcy.comp y hOrbit
  have hA := local_action_derivative_smoothAt n d e q g a U hU σ hσ y hy
  change ContMDiffAt 𝓘(ℝ, RModel q)
    𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
    (gaugeDerivativeCoordinates n d e q g a σ y) y at hA
  have hComp := hC.clm_comp hA
  apply hComp.congr_of_eventuallyEq
  filter_upwards [hEv] with z hz
  change gaugeDerivativeCoordinates n d e q g a σ x z =
    (C z).comp (gaugeDerivativeCoordinates n d e q g a σ y z)
  rw [gaugeDerivativeCoordinates_eq_coordChange_comp n d e q g a σ y z hz.2,
    gaugeDerivativeCoordinates_eq_coordChange_comp n d e q g a σ x z hz.1]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  exact (tangentCoordChange_comp (I := 𝓘(ℝ, RModel q))
    (w := leftCosetAction n (σ z) (baseCoset n))
    (x := leftCosetAction n (σ y) (baseCoset n))
    (y := leftCosetAction n (σ x) (baseCoset n))
    (z := leftCosetAction n (σ z) (baseCoset n))
    ⟨⟨mem_extChartAt_source (I := 𝓘(ℝ, RModel q)) _,
      by simpa only [extChartAt_source] using hz.2⟩,
      by simpa only [extChartAt_source] using hz.1⟩).symm

theorem gaugeDerivativeCoordinates_smoothAt
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x y : ProjectiveCarrier n) (hy : y ∈ U) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (gaugeDerivativeCoordinates n d e q g a σ x) y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hxy
  have hOrbit : ContinuousAt
      (fun z => leftCosetAction n (σ z) (baseCoset n)) y := by
    have hσAt := (hσ.contMDiffAt (hU.mem_nhds hy)).continuousAt
    exact (a.actionSmooth.continuous.continuousAt.comp
      (hσAt.prodMk continuousAt_const))
  have hEv : ∀ᶠ z in 𝓝 y,
      leftCosetAction n (σ z) (baseCoset n) ∈
        (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source ∩
          (chartAt (RModel q) (leftCosetAction n (σ y) (baseCoset n))).source := by
    apply hOrbit.preimage_mem_nhds
    exact ((chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).open_source.inter
      (chartAt (RModel q) (leftCosetAction n (σ y) (baseCoset n))).open_source).mem_nhds
        ⟨hxy, mem_chart_source _ _⟩
  exact gaugeDerivativeCoordinates_smoothAt_of_overlap n d e q g a U hU σ hσ x y hy hxy hEv

end
end QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeDerivativeSmooth
