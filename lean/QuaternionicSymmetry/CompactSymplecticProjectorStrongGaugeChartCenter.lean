import QuaternionicSymmetry.ManifoldChartRefinementCenter
import QuaternionicSymmetry.CompactSymplecticProjectorStrongOrthonormalCoordinateFrame

/-! An arbitrary chart index of the selected strong Euclidean quotient
atlas has a center and its source lies in that center's fixed smooth-gauge
neighborhood. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartCenter

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongChartCenter
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    atlas (EModel q) (ProjectiveCarrier n) → ProjectiveCarrier n := by
  letI := euclideanQuotientCharts n d e q g a
  exact ManifoldChartRefinementCenter.center
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

theorem mem_strongGaugeNeighborhood_of_chart_source
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∀ (i : atlas (EModel q) (ProjectiveCarrier n)) (y : ProjectiveCarrier n),
      y ∈ i.1.source →
      y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
        (strongChartCenter hLee hDesc hImm n d e q g a hq hn i) := by
  letI := euclideanQuotientCharts n d e q g a
  exact ManifoldChartRefinementCenter.mem_neighborhood_of_mem_source
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartCenter
