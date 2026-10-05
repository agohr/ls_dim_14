import QuaternionicSymmetry.CompactSymplecticProjectorBaseStandardQuaternionicStructure

/-! The chosen genuinely orthonormal base frame is also adapted to the
explicit projector-tangent quaternionic I/J, with no independent model-Q
premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseFrameQuaternionicIntertwining

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem baseMetricRowCoordinates_intertwines_I
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseMetricRowCoordinates hDesc hImm n d e q g a hq
        (baseI hDesc hImm n d e q g a hq v) =
      (standardRealQuaternionicStructure n q hq).I
        (baseMetricRowCoordinates hDesc hImm n d e q g a hq v) := by
  letI := a.quotientCharts
  intro v
  let U := standardQuaternionicRealCoordinates n q hq
  let R := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  change U (R (R.symm (QuaternionicMatrixModel.standardI n (R v)))) =
    U (QuaternionicMatrixModel.standardI n (U.symm (U (R v))))
  simp

theorem baseMetricRowCoordinates_intertwines_J
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseMetricRowCoordinates hDesc hImm n d e q g a hq
        (baseJ hDesc hImm n d e q g a hq v) =
      (standardRealQuaternionicStructure n q hq).J
        (baseMetricRowCoordinates hDesc hImm n d e q g a hq v) := by
  letI := a.quotientCharts
  intro v
  let U := standardQuaternionicRealCoordinates n q hq
  let R := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  change U (R (R.symm (QuaternionicMatrixModel.standardJ n (R v)))) =
    U (QuaternionicMatrixModel.standardJ n (U.symm (U (R v))))
  simp

theorem baseOrthonormalFrame_intertwines_I
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      baseI hDesc hImm n d e q g a hq
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v) =
      baseOrthonormalFrame hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).I v) := by
  letI := a.quotientCharts
  intro v
  apply (baseMetricRowCoordinates hDesc hImm n d e q g a hq).injective
  rw [baseMetricRowCoordinates_intertwines_I hDesc hImm n d e q g a hq]
  simp only [baseOrthonormalFrame, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change (standardRealQuaternionicStructure n q hq).I ((1 / 2 : ℝ) • v) =
    (1 / 2 : ℝ) • (standardRealQuaternionicStructure n q hq).I v
  exact map_smul _ _ _

theorem baseOrthonormalFrame_intertwines_J
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      baseJ hDesc hImm n d e q g a hq
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v) =
      baseOrthonormalFrame hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).J v) := by
  letI := a.quotientCharts
  intro v
  apply (baseMetricRowCoordinates hDesc hImm n d e q g a hq).injective
  rw [baseMetricRowCoordinates_intertwines_J hDesc hImm n d e q g a hq]
  simp only [baseOrthonormalFrame, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change (standardRealQuaternionicStructure n q hq).J ((1 / 2 : ℝ) • v) =
    (1 / 2 : ℝ) • (standardRealQuaternionicStructure n q hq).J v
  exact map_smul _ _ _

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseFrameQuaternionicIntertwining
