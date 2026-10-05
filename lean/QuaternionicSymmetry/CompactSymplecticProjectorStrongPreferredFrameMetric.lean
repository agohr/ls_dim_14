import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetricTransport
import QuaternionicSymmetry.CompactSymplecticProjectorTranslatedOrthonormalFrame
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSection
import QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase

/-! The actual frame obtained by translating the explicitly normalized
base projector tangent frame is orthonormal at every selected quotient
point, in that point's preferred strong-chart tangent coordinates. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredFrameMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongGaugeMetricTransport
open CompactSymplecticProjectorTranslatedOrthonormalFrame
open CompactSymplecticProjectorCosetActionBase
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem translatedFrame_strongMetric
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
    let u := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y
    ∀ v w : EModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y
        (euclideanModelEquiv q (translatedOrthonormalFrame hDesc hImm n d e q g a hq u v))
        (euclideanModelEquiv q (translatedOrthonormalFrame hDesc hImm n d e q g a hq u w)) =
      inner ℝ v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  dsimp only
  intro v w
  let u := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y
  rw [strongMetric_eq_originalMetric hLee hDesc hImm n d e q g a hq hn y]
  have hTrans := translatedOrthonormalFrame_metric hDesc hImm n d e q g a hq u v w
  have hy' : leftCosetAction n u (CompactSymplecticProjectorBaseTangent.baseCoset n) = y := by
    rw [leftCosetAction_baseCoset]
    exact strongGaugeSection_right_inverse hLee hDesc hImm n d e q g a hq hn x y hy
  rw [hy'] at hTrans
  exact hTrans

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredFrameMetric
