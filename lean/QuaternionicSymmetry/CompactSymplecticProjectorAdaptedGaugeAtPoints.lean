import QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase

/-! The same actual local section identifies the gauge transition with
the refined tangent-core transition at the literal quotient points y and x. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeAtPoints

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedGaugeCoreSection
open CompactSymplecticProjectorCosetActionBase
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualGauge_core_transition_at_points
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
      (∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        (σ y : ProjectiveCarrier n) = y) ∧
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
              (achart (EModel q) y) (achart (EModel q) x) y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  obtain ⟨σ, hRight, hSmooth, hData⟩ :=
    actualGauge_section_smooth_span_and_core_transition
      hLee hDesc hImm n d e q g a hq hn x
  refine ⟨σ, hRight, hSmooth, ?_⟩
  intro y hy
  obtain ⟨C, hSpan, hCore⟩ := hData y hy
  refine ⟨C, hSpan, ?_⟩
  simpa only [leftCosetAction_baseCoset,
    hRight y hy,
    hRight x (mem_actualGaugeNeighborhood hLee hDesc hImm
      n d e q g a hq hn x)] using hCore

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeAtPoints
