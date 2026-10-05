import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSmoothTransport

/-! The selected local quotient representative is genuinely smooth on the
strong Euclidean gauge chart and remains a right inverse there. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSection

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSmoothTransport
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def strongGaugeSection
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) : ProjectiveCarrier n → G n :=
  Classical.choose ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)

theorem strongGaugeSection_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, RModel d) ∞
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  have hOld : ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
    hSpec.1.mono Set.inter_subset_right
  exact contMDiffOn_strongGauge_of_original hLee hDesc hImm
    n d e q g a hq hn
    (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x)
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
    hOld

theorem strongGaugeSection_right_inverse
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y :
      ProjectiveCarrier n) = y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  exact hSpec.2.1 y hy.2

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSection
