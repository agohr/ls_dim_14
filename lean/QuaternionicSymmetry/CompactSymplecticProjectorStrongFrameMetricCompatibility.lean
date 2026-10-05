import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameCoreCancellation
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredFrameMetric

/-! The actual smooth local tangent frame is orthonormal for the concrete
Frobenius projector metric after the genuine core transition from its
strong chart to the point's preferred tangent chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCompatibility

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongFrameCoreCancellation
open CompactSymplecticProjectorStrongPreferredFrameMetric
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localStrongFrame_metric_orthonormal
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ v w : EModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y
        (tangentCoordChange 𝓘(ℝ, EModel q) x y y
          (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y v))
        (tangentCoordChange 𝓘(ℝ, EModel q) x y y
          (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y w)) =
      inner ℝ v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  intro v w
  rw [localFrame_coreChange_to_preferred hLee hDesc hImm n d e q g a hq hn x y hy v,
    localFrame_coreChange_to_preferred hLee hDesc hImm n d e q g a hq hn x y hy w]
  exact translatedFrame_strongMetric hLee hDesc hImm n d e q g a hq hn x y hy v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCompatibility
