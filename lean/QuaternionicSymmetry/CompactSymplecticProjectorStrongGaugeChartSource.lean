import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanCharts
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas

/-! Membership in a selected strong gauge neighborhood supplies the
actual source-overlap needed for tangent-core cocycle cancellation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartSource

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorCosetActionBase
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem mem_strongGauge_extendedChart_source
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    y ∈ (extChartAt 𝓘(ℝ, EModel q) x).source := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  have hOverlap := hSpec.2.2.1 y hy.2
  have hx : leftCosetAction n (σ x) (baseCoset n) = x := by
    rw [leftCosetAction_baseCoset]
    exact strongGaugeSection_right_inverse hLee hDesc hImm n d e q g a hq hn x x
      (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
  have hy' : leftCosetAction n (σ y) (baseCoset n) = y := by
    rw [leftCosetAction_baseCoset]
    exact strongGaugeSection_right_inverse hLee hDesc hImm n d e q g a hq hn x y hy
  change leftCosetAction n (σ y) (baseCoset n) ∈
    (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source at hOverlap
  rw [hx, hy'] at hOverlap
  have hOld : y ∈ (chartAt (RModel q) x).source := hOverlap
  have hEuclidean :
      (letI := euclideanQuotientCharts n d e q g a
       y ∈ (chartAt (EModel q) x).source) := by
    letI := euclideanQuotientCharts n d e q g a
    rw [euclideanQuotientCharts_chartAt]
    simpa using hOld
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  rw [extChartAt_source]
  change y ∈ (((letI := euclideanQuotientCharts n d e q g a
    chartAt (EModel q) x)).restr
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)).source
  rw [((letI := euclideanQuotientCharts n d e q g a
    chartAt (EModel q) x)).restr_source'
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn x)]
  exact ⟨hEuclidean, hy⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartSource
