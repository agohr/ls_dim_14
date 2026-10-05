import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicGenerators

/-! The third locally conjugated projector-tangent generator is also
intertwined with the standard Euclidean quaternionic K = I ∘ J,
derived from the checked first two generators. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicK

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorBaseFrameQuaternionicIntertwining
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongFrameOperatorIntertwining
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localFrame_intertwines_K
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      euclideanLocalConjugateOperator n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseK hDesc hImm n d e q g a hq).toLinearMap) y
        (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y v) =
      localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y
        ((standardRealQuaternionicStructure n q hq).K v) := by
  letI := a.quotientCharts
  intro v
  apply selectedOperator_intertwines_localFrame hLee hDesc hImm
    n d e q g a hq hn x y hy
    (Module.End.toContinuousLinearMap (RModel q)
      (baseK hDesc hImm n d e q g a hq).toLinearMap)
    ((standardRealQuaternionicStructure n q hq).K.toContinuousLinearEquiv.toContinuousLinearMap)
  intro z
  change (euclideanModelEquiv q)
      (baseI hDesc hImm n d e q g a hq
        (baseJ hDesc hImm n d e q g a hq
          (baseOrthonormalFrame hDesc hImm n d e q g a hq z))) =
    (euclideanModelEquiv q)
      (baseOrthonormalFrame hDesc hImm n d e q g a hq
        ((standardRealQuaternionicStructure n q hq).I
          ((standardRealQuaternionicStructure n q hq).J z)))
  rw [baseOrthonormalFrame_intertwines_J hDesc hImm n d e q g a hq,
    baseOrthonormalFrame_intertwines_I hDesc hImm n d e q g a hq]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicK
