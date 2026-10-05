import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorEquiv
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.ManifoldTwistorSphereHomeomorph

/-! The concrete associated-to-actual twistor bijection is a homeomorphism.
Its inverse continuity is deduced from compactness and Hausdorffness after
the forward map's genuine quotient continuity has been proved. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorHomeomorph

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorAssociatedActualTwistorEquiv
open CompactSymplecticProjectorAssociatedActualTwistorContinuous
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereManifold
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

def associatedActualTwistorHomeomorph
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
    AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq) ≃ₜ
      TwistorSphere (strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI : CompactSpace coefficientSphere := coefficientSphereHomeomorph.symm.compactSpace
  letI : CompactSpace (AssociatedSphereFiber n
      (standardRealQuaternionicStructure n q hq)) := Quotient.compactSpace
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  letI : T2Space (TwistorSphere Q) := (sphereTotalHomeomorph Q).symm.isEmbedding.t2Space
  let E := associatedActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
  have hc : Continuous E := continuous_associatedSphereToActualTwistor hR3
    hLee hDesc hImm n d e q g a hq hn
  exact E.toHomeomorphOfContinuousClosed hc hc.isClosedMap

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorHomeomorph
