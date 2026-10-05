import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasQuaternionicGauge

/-! Constant conjugation by the canonical Euclidean coordinate equivalence
turns the actual local quaternionic operators into smooth Euclidean-model fields. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasEuclideanGauge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasQuaternionicGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def euclideanLocalConjugateOperator
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x : ProjectiveCarrier n)
    (S : RModel q →L[ℝ] RModel q) (y : ProjectiveCarrier n) :
    EModel q →L[ℝ] EModel q :=
  (euclideanModelEquiv q).toContinuousLinearMap.comp
    ((localConjugateOperator n d e q g a σ x S y).comp
      (euclideanModelEquiv q).symm.toContinuousLinearMap)

theorem actualEuclideanGauge_smooth_on_adaptedNeighborhood
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
    ∃ σ : ProjectiveCarrier n → G n,
      (∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        (σ y : ProjectiveCarrier n) = y) ∧
      ∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
          (euclideanLocalConjugateOperator n d e q g a σ x S)
          (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  obtain ⟨σ, hRight, hSmooth⟩ := actualGauge_smooth_on_adaptedNeighborhood
    hLee hDesc hImm n d e q g a hq hn x
  refine ⟨σ, hRight, ?_⟩
  intro S
  let W := actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x
  have hL : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, RModel q →L[ℝ] EModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).toContinuousLinearMap) W := contMDiffOn_const
  have hR : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, EModel q →L[ℝ] RModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).symm.toContinuousLinearMap) W := contMDiffOn_const
  exact (hL.clm_comp (hSmooth S)).clm_comp hR

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
