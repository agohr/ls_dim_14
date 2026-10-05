import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge
import QuaternionicSymmetry.CompactSymplecticProjectorBaseFrameQuaternionicIntertwining
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan

/-! At the base point, the Euclidean coordinate version of the proved
metric-orthonormal frame intertwines the actual projector-tangent I/J with
the fixed Euclidean quaternionic I/J. Variable strong-chart transport is
a separate next step. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicIntertwining

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseFrameQuaternionicIntertwining
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem baseEuclideanFrame_intertwines_I
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      (euclideanModelEquiv q).toContinuousLinearMap
        ((Module.End.toContinuousLinearMap (RModel q)
          (baseI hDesc hImm n d e q g a hq).toLinearMap)
          ((euclideanModelEquiv q).symm
            (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq v))) =
      baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).I v) := by
  letI := a.quotientCharts
  intro v
  change (euclideanModelEquiv q)
      (baseI hDesc hImm n d e q g a hq
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v)) =
    (euclideanModelEquiv q)
      (baseOrthonormalFrame hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).I v))
  rw [baseOrthonormalFrame_intertwines_I hDesc hImm n d e q g a hq]

theorem baseEuclideanFrame_intertwines_J
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      (euclideanModelEquiv q).toContinuousLinearMap
        ((Module.End.toContinuousLinearMap (RModel q)
          (baseJ hDesc hImm n d e q g a hq).toLinearMap)
          ((euclideanModelEquiv q).symm
            (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq v))) =
      baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).J v) := by
  letI := a.quotientCharts
  intro v
  change (euclideanModelEquiv q)
      (baseJ hDesc hImm n d e q g a hq
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v)) =
    (euclideanModelEquiv q)
      (baseOrthonormalFrame hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).J v))
  rw [baseOrthonormalFrame_intertwines_J hDesc hImm n d e q g a hq]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicIntertwining
