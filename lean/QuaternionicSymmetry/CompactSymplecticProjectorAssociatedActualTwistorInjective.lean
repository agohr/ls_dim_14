import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorSurjective
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorInjective

/-! The descended associated-sphere map identifies no more points than
the actual first-pair stabilizer relation: it is injective into the LC
twistor total space. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorInjective

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorAssociatedActualTwistorBase
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseTwistorInjective
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
private abbrev K (n : ℕ) := firstPairStabilizer n

theorem associatedSphereToActualTwistor_injective
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
    Function.Injective
      (associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  intro A B hAB
  induction A using Quotient.inductionOn with
  | _ A =>
    induction B using Quotient.inductionOn with
    | _ B =>
      have hbase : (A.1 : ProjectiveCarrier n) = (B.1 : ProjectiveCarrier n) := by
        have h := congrArg (projection Q) hAB
        rw [associatedSphereToActualTwistor_base,
          associatedSphereToActualTwistor_base] at h
        exact h
      have hmem : A.1⁻¹ * B.1 ∈ K n := QuotientGroup.eq.mp hbase
      let k : K n := ⟨A.1⁻¹ * B.1, hmem⟩
      have hgroup : B.1 * (k⁻¹ : G n) = A.1 := by
        simp [k, mul_assoc]
      have hfiberPoint : strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn A.2 =
          strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • B.2) := by
        have hAction : A.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn A.2 =
            A.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • B.2) := calc
          A.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn A.2 =
              B.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn B.2 := by
                simpa only [associatedSphereToActualTwistor_mk] using hAB
          _ = (B.1 * (k⁻¹ : G n)) •
                strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • B.2) := by
                rw [← strongBaseTwistorPoint_stabilizer hLee hDesc hImm n d e q g a hq hn k B.2]
                rw [← mul_smul]
                simp only [mul_assoc, inv_mul_cancel, mul_one]
          _ = A.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn (k • B.2) := by
                rw [hgroup]
        have hcancel := congrArg
          (fun p : TwistorSphere Q => A.1⁻¹ • p) hAction
        simpa only [← mul_smul, inv_mul_cancel, one_smul] using hcancel
      have hfiber : A.2 = k • B.2 :=
        (strongBaseTwistorPoint_injective hLee hDesc hImm n d e q g a hq hn) hfiberPoint
      apply Quotient.sound
      change ∃ l : K n, (associatedAction n).smul l B = A
      exact ⟨k, Prod.ext hgroup hfiber.symm⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorInjective
