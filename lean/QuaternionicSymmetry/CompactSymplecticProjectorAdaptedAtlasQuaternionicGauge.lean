import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasLocalSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! The actual projector quotient's local quaternionic gauge remains
C-infinity in the genuinely refined Euclidean source charts. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasQuaternionicGauge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorActualSmoothQuaternionicPlane
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasLocalSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualGauge_smooth_on_adaptedNeighborhood
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
      (∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
          (localConjugateOperator n d e q g a σ x S)
          (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨σ, hRight, hSmooth, _⟩ :=
    (Classical.choose_spec
      (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
        n d e q g a hq hn x)).2.2
  refine ⟨σ, hRight, ?_⟩
  intro S
  exact contMDiffOn_adaptedAtlas_of_original hLee hDesc hImm
    n d e q g a hq hn
    (localConjugateOperator n d e q g a σ x S)
    (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
    (hSmooth S)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasQuaternionicGauge
