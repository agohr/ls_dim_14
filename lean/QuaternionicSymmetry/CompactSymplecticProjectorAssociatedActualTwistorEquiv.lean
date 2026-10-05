import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorInjective

/-! The associated coefficient-sphere bundle and the actual
Levi-Civita-derived quaternionic twistor sphere have the same points over
the true HP projector quotient. Topology, smoothness, complex and contact
compatibility remain separate obligations. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorEquiv

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorAssociatedActualTwistorBase
open CompactSymplecticProjectorAssociatedActualTwistorSurjective
open CompactSymplecticProjectorAssociatedActualTwistorInjective
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

def associatedActualTwistorEquiv
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
    AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq) ≃
      TwistorSphere (strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact Equiv.ofBijective
    (associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn)
    ⟨associatedSphereToActualTwistor_injective hLee hDesc hImm n d e q g a hq hn,
      associatedSphereToActualTwistor_surjective hLee hDesc hImm n d e q g a hq hn⟩

theorem associatedActualTwistorEquiv_base
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
      (associatedActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn z) =
      sphereBase n (standardRealQuaternionicStructure n q hq) z := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact associatedSphereToActualTwistor_base hLee hDesc hImm n d e q g a hq hn z

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorEquiv
