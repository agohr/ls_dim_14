import QuaternionicSymmetry.CompactSymplecticProjectorBaseMetricRow

/-! A fixed real orthonormal coordinate model for the checked standard
quaternionic row. Combined with the exact factor-four base metric formula,
this produces an actual metric-orthonormal model frame. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseOrthonormalCoordinates

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseMetricRow
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def standardQuaternionicRealCoordinates (n q : ℕ) (hq : q = 4 * n) :
    QuaternionicMatrixModel.V n ≃ₗᵢ[ℝ] EModel q :=
  (stdOrthonormalBasis ℝ (QuaternionicMatrixModel.V n)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr ((QuaternionicMatrixModel.real_finrank_eq_four_mul n).trans hq.symm)))

def baseMetricRowCoordinates
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃L[ℝ] EModel q := by
  letI := a.quotientCharts
  letI : FiniteDimensional ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := by
    change FiniteDimensional ℝ (RModel q)
    infer_instance
  exact (baseTangentEuclideanEquiv hDesc hImm n d e q g a hq).toContinuousLinearEquiv.trans
    (standardQuaternionicRealCoordinates n q hq).toContinuousLinearEquiv

theorem baseMetricRowCoordinates_metric
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (CompactSymplecticProjectorRiemannianMetric.smoothProjectorMetric
        hDesc hImm n d e q g a).inner (baseCoset n) v w =
        4 * inner ℝ
          (baseMetricRowCoordinates hDesc hImm n d e q g a hq v)
          (baseMetricRowCoordinates hDesc hImm n d e q g a hq w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  rw [actual_base_metric_euclidean hDesc hImm n d e q g a hq v w]
  simp only [baseMetricRowCoordinates, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact congrArg (fun t : ℝ => 4 * t)
    ((standardQuaternionicRealCoordinates n q hq).inner_map_map
      (baseTangentEuclideanEquiv hDesc hImm n d e q g a hq v)
      (baseTangentEuclideanEquiv hDesc hImm n d e q g a hq w)).symm

def halfEuclidean (q : ℕ) : EModel q ≃L[ℝ] EModel q :=
  ContinuousLinearEquiv.equivOfInverse
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EModel q))
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (EModel q))
    (by
      intro v
      change (2 : ℝ) • ((1 / 2 : ℝ) • v) = v
      rw [smul_smul]
      norm_num)
    (by
      intro v
      change (1 / 2 : ℝ) • ((2 : ℝ) • v) = v
      rw [smul_smul]
      norm_num)

def baseOrthonormalFrame
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    EModel q ≃L[ℝ] TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) := by
  letI := a.quotientCharts
  exact (halfEuclidean q).trans
    (baseMetricRowCoordinates hDesc hImm n d e q g a hq).symm

theorem baseOrthonormalFrame_metric
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : EModel q,
      (CompactSymplecticProjectorRiemannianMetric.smoothProjectorMetric
        hDesc hImm n d e q g a).inner (baseCoset n)
          (baseOrthonormalFrame hDesc hImm n d e q g a hq v)
          (baseOrthonormalFrame hDesc hImm n d e q g a hq w) =
        inner ℝ v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  rw [baseMetricRowCoordinates_metric hDesc hImm n d e q g a hq]
  simp only [baseOrthonormalFrame, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change 4 * inner ℝ ((1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • w) = inner ℝ v w
  simp [real_inner_smul_left, real_inner_smul_right]
  ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseOrthonormalCoordinates
