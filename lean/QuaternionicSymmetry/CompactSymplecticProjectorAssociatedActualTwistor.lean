import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPointEquivariance
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopf

/-! The checked associated coefficient-sphere bundle descends into the
actual derivative-defined LC twistor sphere, not an abstract model copy.
Stabilizer independence follows from the exact intrinsic isotropy action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistor

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseTwistorPointEquivariance
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
set_option maxHeartbeats 1000000

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def associatedSphereToActualTwistor
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq) →
      TwistorSphere (strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  refine Quotient.lift (fun z : G n × coefficientSphere =>
    z.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z.2) ?_
  intro b c hbc
  change ∃ k : firstPairStabilizer n, (associatedAction n).smul k c = b at hbc
  rcases hbc with ⟨k, rfl⟩
  change (c.1 * (k⁻¹ : G n)) •
      strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • c.2) =
    c.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn c.2
  rw [← strongBaseTwistorPoint_stabilizer hLee hDesc hImm n d e q g a hq hn k c.2]
  rw [← mul_smul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

@[simp] theorem associatedSphereToActualTwistor_mk
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (u : G n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
    letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
    associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn
      (⟦(u,z)⟧ : AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq)) =
      u • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  simp only [associatedSphereToActualTwistor, Quotient.lift_mk]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistor
