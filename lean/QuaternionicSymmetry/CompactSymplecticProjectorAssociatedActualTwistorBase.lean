import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistor
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedBase

/-! The descended map to the actual LC twistor sphere preserves the
genuine HP projector base projection. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorBase

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

theorem associatedSphereToActualTwistor_base
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q]
    (z : AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq)) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    projection (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn z) =
      sphereBase n (standardRealQuaternionicStructure n q hq) z := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  induction z using Quotient.inductionOn with
  | _ z =>
      rw [associatedSphereToActualTwistor_mk]
      rw [strongTwistorAction_projection,
        strongBaseTwistorPoint_base]
      change leftCosetAction n z.1 (baseCoset n) = (z.1 : ProjectiveCarrier n)
      change ((z.1 * 1 : CompactSymplecticHaar.Group (n + 1)) : ProjectiveCarrier n) = _
      rw [mul_one]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorBase
