import QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelTangentFormula
import QuaternionicSymmetry.ManifoldChartRefinementTargetDifferential

/-! The actual identity diffeomorphism from the original quotient atlas to
the strong Euclidean atlas has the canonical real-to-Euclidean differential
at every coset, not merely an unspecified tangent equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorOldToStrongTangent

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorEuclideanModelTangentFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementTargetDifferential
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem oldToStrong_mfderiv_eq_coordinateEquiv
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, EModel q)
      (oldToStrongDiffeomorph hLee hDesc hImm n d e q g a hq hn :
        ProjectiveCarrier n → ProjectiveCarrier n) x =
      (euclideanModelEquiv q).toContinuousLinearMap := by
  letI := a.quotientCharts
  let oldCharts := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  let selfCharts := euclideanQuotientCharts n d e q g a
  letI := selfCharts
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let W := strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
  let strongCharts := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let U := (euclideanModelEquiv q).toContinuousLinearMap
  have hModel : @HasMFDerivAt ℝ _ (RModel q) _ _ (RModel q) _
      𝓘(ℝ, RModel q) (ProjectiveCarrier n) _ oldCharts
      (EModel q) _ _ (RModel q) _ (euclideanModel q)
      (ProjectiveCarrier n) _ oldCharts
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x U := by
    have h := (euclideanModelDiffeomorph n d e q g a).contMDiff_toFun.mdifferentiableAt
      (x := x) (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hd := h.hasMFDerivAt
    change HasMFDerivAt 𝓘(ℝ, RModel q) (euclideanModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x
      (mfderiv 𝓘(ℝ, RModel q) (euclideanModel q)
        (id : ProjectiveCarrier n → ProjectiveCarrier n) x) at hd
    rw [euclideanModelIdentity_mfderiv_eq_linearEquiv n d e q g a x] at hd
    exact hd
  have hSelf : @HasMFDerivAt ℝ _ (RModel q) _ _ (RModel q) _
      𝓘(ℝ, RModel q) (ProjectiveCarrier n) _ oldCharts
      (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ selfCharts
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x U := by
    simpa [HasMFDerivAt, writtenInExtChartAt, euclideanQuotient_extendedChart_eq,
      euclideanModel, ModelWithCorners.transContinuousLinearEquiv_range] using hModel
  have hStrong : @HasMFDerivAt ℝ _ (RModel q) _ _ (RModel q) _
      𝓘(ℝ, RModel q) (ProjectiveCarrier n) _ oldCharts
      (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ strongCharts
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x U := by
    simpa [HasMFDerivAt, writtenInExtChartAt, extChartAt,
      strongEuclideanQuotientCharts, ManifoldChartRefinement.restrictedCharts,
      mfld_simps] using hSelf
  change @mfderiv ℝ _ (RModel q) _ _ (RModel q) _
      𝓘(ℝ, RModel q) (ProjectiveCarrier n) _ oldCharts
      (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ strongCharts
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x = U
  exact hStrong.mfderiv

end
end QuaternionicSymmetry.CompactSymplecticProjectorOldToStrongTangent
