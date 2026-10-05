import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartSource

/-! The genuine strong tangent-core transition cancels the fixed-chart
expression of the selected action frame, recovering exactly the actual
translated frame in preferred coordinates. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameCoreCancellation

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongFrameMetricCoordinate
open CompactSymplecticProjectorStrongGaugeChartSource
open CompactSymplecticProjectorTranslatedOrthonormalFrame
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localFrame_coreChange_to_preferred
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ v : EModel q,
      tangentCoordChange 𝓘(ℝ, EModel q) x y y
        (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y v) =
      euclideanModelEquiv q
        (translatedOrthonormalFrame hDesc hImm n d e q g a hq
          (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y) v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  intro v
  rw [localOrthonormalFromFrame_eq_charted_translatedFrame
    hLee hDesc hImm n d e q g a hq hn x y hy v]
  have hSourceX := mem_strongGauge_extendedChart_source
    hLee hDesc hImm n d e q g a hq hn x y hy
  have hSourceY : y ∈ (extChartAt 𝓘(ℝ, EModel q) y).source :=
    mem_extChartAt_source y
  have hTriple : y ∈ (extChartAt 𝓘(ℝ, EModel q) y).source ∩
      (extChartAt 𝓘(ℝ, EModel q) x).source ∩
      (extChartAt 𝓘(ℝ, EModel q) y).source :=
    ⟨⟨hSourceY, hSourceX⟩, hSourceY⟩
  rw [tangentCoordChange_comp (I := 𝓘(ℝ, EModel q))
    (w := y) (x := x) (y := y) (z := y) (h := hTriple)]
  rw [tangentCoordChange_self hSourceY]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameCoreCancellation
