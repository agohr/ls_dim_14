import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelPlane

/-! The two Euclidean chart realizations have identical extended charts,
so their genuine identity-map differential is the identity CLM. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridgeTangent

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem euclideanChartIdentity_mfderiv_eq_id
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    mfderiv (euclideanModel q) 𝓘(ℝ, EModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x =
      ContinuousLinearMap.id ℝ (EModel q) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  have hOld : HasMFDerivAt (euclideanModel q) (euclideanModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x
      (ContinuousLinearMap.id ℝ (EModel q)) := hasMFDerivAt_id x
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  have hNew : HasMFDerivAt (euclideanModel q) 𝓘(ℝ, EModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x
      (ContinuousLinearMap.id ℝ (EModel q)) := by
    simpa [HasMFDerivAt, writtenInExtChartAt,
      euclideanQuotient_extendedChart_eq, euclideanModel,
      ModelWithCorners.transContinuousLinearEquiv_range] using hOld
  exact hNew.mfderiv

theorem selfModelTangentEquiv_eq_refl
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    selfModelTangentEquiv n d e q g a x =
      ContinuousLinearEquiv.refl ℝ (EModel q) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  apply ContinuousLinearEquiv.ext
  funext v
  change mfderiv (euclideanModel q) 𝓘(ℝ, EModel q)
    (id : ProjectiveCarrier n → ProjectiveCarrier n) x v = v
  rw [euclideanChartIdentity_mfderiv_eq_id n d e q g a x]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridgeTangent
