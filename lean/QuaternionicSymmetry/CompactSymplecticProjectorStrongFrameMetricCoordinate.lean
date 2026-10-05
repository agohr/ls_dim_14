import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeEuclideanDerivativeCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredFrameMetric
import QuaternionicSymmetry.CompactSymplecticProjectorStrongOrthonormalCoordinateFrame

/-! The smooth local strong-chart frame is exactly the chart-coordinate
image of the genuinely translated orthonormal projector tangent frame.
This is the coordinate identity needed before metric/Q overlap laws. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongGaugeEuclideanDerivativeCoordinate
open CompactSymplecticProjectorTranslatedOrthonormalFrame
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localOrthonormalFromFrame_eq_charted_translatedFrame
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
    let u := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y
    ∀ v : EModel q,
      localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y v =
        tangentCoordChange 𝓘(ℝ, EModel q) y x y
          (euclideanModelEquiv q
            (translatedOrthonormalFrame hDesc hImm n d e q g a hq u v)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  dsimp only
  intro v
  let u := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x y
  have hD := selected_euclideanGaugeDerivative_eq_charted_translation
    hLee hDesc hImm n d e q g a hq hn x y hy
  change (euclideanGaugeDerivative n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y)
      ((euclideanModelEquiv q)
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v)) = _
  rw [hD]
  simp only [ContinuousLinearMap.comp_apply]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCoordinate
