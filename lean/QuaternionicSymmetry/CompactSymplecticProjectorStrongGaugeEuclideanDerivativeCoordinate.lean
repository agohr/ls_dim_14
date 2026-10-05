import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeTransition

/-! The selected action derivative in the genuine strong Euclidean tangent
chart is the actual base-point differential followed by its true tangent
core coordinate transition. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeEuclideanDerivativeCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticProjectorStrongGaugeDerivativeCoordinate
open CompactSymplecticProjectorStrongGaugeTransition
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem selected_euclideanGaugeDerivative_eq_charted_translation
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
    let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
    euclideanGaugeDerivative n d e q g a σ x y =
      (tangentCoordChange 𝓘(ℝ, EModel q) y x y).comp
        ((euclideanModelEquiv q).toContinuousLinearMap.comp
          ((mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
            (leftCosetAction n (σ y)) (baseCoset n)).comp
            (euclideanModelEquiv q).symm.toContinuousLinearMap)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by norm_cast)
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  have hOld := selected_gaugeDerivativeCoordinates_eq_charted_translation
    hLee hDesc hImm n d e q g a hq hn x y hy
  have hChart := strong_tangentCoordChange_eq_original_conj
    hLee hDesc hImm n d e q g a hq hn y x y
  apply ContinuousLinearMap.ext
  intro v
  simp only [euclideanGaugeDerivative, ContinuousLinearMap.comp_apply]
  rw [hOld, hChart]
  simp only [ContinuousLinearMap.comp_apply]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeEuclideanDerivativeCoordinate
