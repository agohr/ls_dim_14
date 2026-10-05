import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseIntrinsicEquivariance
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorAction
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint

/-! The concrete coefficient-sphere parametrization of the actual LC
twistor base fiber intertwines the literal projector stabilizer action
with the derivative-induced action on the strong twistor sphere. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPointEquivariance

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseIntrinsicEquivariance
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorStrongTranslationHom
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicDerivativeAction
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

theorem strongBaseTwistorPoint_stabilizer
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q]
    (k : firstPairStabilizer n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
    letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
    (k.1 : CompactSymplecticHaar.Group (n+1)) •
      strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z =
      strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • z) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := (translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn) k.1
  have hfix : f • baseCoset n = baseCoset n :=
    stabilizer_fixes_baseCoset n k.1 k.2
  have hCast {x y : ProjectiveCarrier n} (h : x = y)
      (B : IntrinsicTwistorFiber Q x) :
      preferredPoint Q x ((preferredFiberEquiv Q x).symm B) =
      preferredPoint Q y ((preferredFiberEquiv Q y).symm (h ▸ B)) := by
    cases h
    rfl
  change twistorMap Q f
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z) = _
  unfold twistorMap
  change preferredPoint Q (f • baseCoset n)
      ((preferredFiberEquiv Q (f • baseCoset n)).symm
        (intrinsicTwistorFiberAction Q f (baseCoset n)
          (toIntrinsicFiber Q
            (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z)))) = _
  rw [strongBaseTwistorPoint_intrinsic]
  rw [hCast hfix]
  rw [strongBaseIntrinsicFiberPoint_stabilizer hLee hDesc hImm n d e q g a hq hn k z]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPointEquivariance
