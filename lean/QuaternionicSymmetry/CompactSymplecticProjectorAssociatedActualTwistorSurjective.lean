import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorBase
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquiv
import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDiffeomorph

/-! Every actual LC twistor point is a symplectic translate of the
explicitly identified base twistor fiber. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorSurjective

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseTwistorEquiv
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorTranslationDiffeomorph
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

theorem associatedSphereToActualTwistor_surjective
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
    Function.Surjective
      (associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  intro p
  obtain ⟨u, hu⟩ := Quotient.exists_rep (projection Q p)
  have hbase : projection Q (u⁻¹ • p) = baseCoset n := by
    rw [strongTwistorAction_projection, ← hu]
    change ((u⁻¹ * u : G n) : ProjectiveCarrier n) = baseCoset n
    rw [inv_mul_cancel]
    rfl
  obtain ⟨z, hz⟩ := (strongBaseTwistorFiberEquiv hLee hDesc hImm n d e q g a hq hn).surjective
    (⟨u⁻¹ • p, hbase⟩ : strongBaseTwistorFiber hLee hDesc hImm n d e q g a hq hn)
  refine ⟨(⟦(u,z)⟧ : AssociatedSphereFiber n
    (standardRealQuaternionicStructure n q hq)), ?_⟩
  rw [associatedSphereToActualTwistor_mk]
  have hp : strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z =
      u⁻¹ • p := congrArg Subtype.val hz
  rw [hp, ← mul_smul, mul_inv_cancel, one_smul]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorSurjective
