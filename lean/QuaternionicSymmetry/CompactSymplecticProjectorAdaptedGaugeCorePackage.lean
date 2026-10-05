import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreTransition

/-! The genuine local smooth Q-frame, exact Q-span, and actual refined
tangent-core coordinate transition are packaged for the same local section. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCorePackage

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorAdaptedAtlasGaugePlane
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedGaugeCoreTransition
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualGauge_smooth_span_and_core_transition
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (adaptedEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    ∃ σ : ProjectiveCarrier n → G n,
      (∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
          (euclideanLocalConjugateOperator n d e q g a σ x S)
          (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)) ∧
      ∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        ∃ C : RModel q ≃L[ℝ] RModel q,
          euclideanLocalFrameSpan hDesc hImm n d e q g a hq σ x y =
            ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
              ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
              (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) ∧
          (euclideanModelEquiv q).toContinuousLinearMap.comp
            ((C : RModel q →L[ℝ] RModel q).comp
              (euclideanModelEquiv q).symm.toContinuousLinearMap) =
            (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
              (achart (EModel q) (leftCosetAction n (σ y) (baseCoset n)))
              (achart (EModel q) (leftCosetAction n (σ x) (baseCoset n)))
              (leftCosetAction n (σ y) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  obtain ⟨σ, hSmooth, hPlane⟩ := adaptedGauge_smooth_and_spans_actual_plane
    hLee hDesc hImm n d e q g a hq hn x
  refine ⟨σ, hSmooth, ?_⟩
  intro y hy
  obtain ⟨C, hC, hSpan⟩ := hPlane y hy
  refine ⟨C, hSpan, ?_⟩
  exact localChartChange_eq_adaptedTangentCore hLee hDesc hImm
    n d e q g a hq hn σ x y C hC

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCorePackage
