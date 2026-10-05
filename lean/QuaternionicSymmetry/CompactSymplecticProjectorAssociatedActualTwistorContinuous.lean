import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistor
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorActionContinuous

/-! The concrete stabilizer-independent associated-space map into the
Levi-Civita twistor sphere is continuous for the quotient topology. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorContinuous

open Manifold
open Topology
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorStrongBaseTwistorContinuous
open CompactSymplecticProjectorStrongTwistorActionContinuous
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem continuous_associatedSphereToActualTwistor
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
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
    Continuous (associatedSphereToActualTwistor hLee hDesc hImm
      n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := CompactSymplecticProjectorStabilizerHopfAction.sphereFiberAction n
    (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let s := @MulAction.orbitRel (firstPairStabilizer n)
    (G n × coefficientSphere) _ (associatedAction n)
  have hquot : IsQuotientMap (@Quotient.mk' (G n × coefficientSphere) s) :=
    isQuotientMap_quotient_mk'
  apply hquot.continuous_iff.mpr
  have hpair : Continuous (fun p : G n × coefficientSphere =>
      (p.1, strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn p.2)) :=
    continuous_fst.prodMk
      ((continuous_strongBaseTwistorPoint hLee hDesc hImm
        n d e q g a hq hn).comp continuous_snd)
  have h := (continuous_strongTwistorAction hR3 hLee hDesc hImm
    n d e q g a hq hn).comp hpair
  exact h.congr (fun p => by
    change associatedSphereToActualTwistor hLee hDesc hImm
      n d e q g a hq hn (⟦p⟧ : AssociatedSphereFiber n
        (standardRealQuaternionicStructure n q hq)) =
        p.1 • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn p.2
    exact associatedSphereToActualTwistor_mk hLee hDesc hImm
      n d e q g a hq hn p.1 p.2)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorContinuous
