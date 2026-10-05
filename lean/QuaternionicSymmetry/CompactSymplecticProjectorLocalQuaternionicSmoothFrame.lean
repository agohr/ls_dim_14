import QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeFrameSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInvertible

/-! One fixed open quotient gauge supports C-infinity coordinate
operators for every base tangent endomorphism, simultaneously. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicSmoothFrame

open Manifold Filter Set
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorFixedGaugeFrameSmooth
open CompactSymplecticProjectorLocalDerivativeInvertible
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localQuaternionicSmoothFrame
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x : ProjectiveCarrier n) (hx : x ∈ U) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∃ W : Set (ProjectiveCarrier n), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      (∀ y ∈ W, leftCosetAction n (σ y) (baseCoset n) ∈
        (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source) ∧
      (∀ y ∈ W, ∃ E : RModel q ≃L[ℝ] RModel q,
        (E : RModel q →L[ℝ] RModel q) =
          gaugeDerivativeCoordinates n d e q g a σ x y) ∧
      ∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
          (localConjugateOperator n d e q g a σ x S) W := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨V, hVopen, hxV, hVU, hVinv⟩ :=
    gaugeDerivativeCoordinates_locally_invertible n d e q g a U hU σ hσ x hx
  have hOrbit : ContinuousAt
      (fun y => leftCosetAction n (σ y) (baseCoset n)) x := by
    have hσAt := (hσ.contMDiffAt (hU.mem_nhds hx)).continuousAt
    exact a.actionSmooth.continuous.continuousAt.comp
      (hσAt.prodMk continuousAt_const)
  have hPre : {y : ProjectiveCarrier n |
      leftCosetAction n (σ y) (baseCoset n) ∈
        (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source} ∈ 𝓝 x :=
    hOrbit.preimage_mem_nhds
      ((chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).open_source.mem_nhds
        (mem_chart_source _ _))
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp
    (inter_mem (hVopen.mem_nhds hxV) hPre)
  refine ⟨W, hWopen, hxW, (fun y hy => hVU (hWsub hy).1),
    (fun y hy => (hWsub hy).2), (fun y hy => hVinv y (hWsub hy).1), ?_⟩
  intro S y hy
  exact (localConjugateOperator_smoothAt_of_overlap n d e q g a U hU σ hσ
    x y (hVU (hWsub hy).1) S (hWsub hy).2
    (hVinv y (hWsub hy).1)).contMDiffWithinAt

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicSmoothFrame
