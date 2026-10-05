import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorEquiv
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientEquiv

/-! The independently checked complex-projective total space and the
actual Levi-Civita twistor sphere of the projector HP model have a
base-preserving set equivalence. The associated Hopf identification here
uses the corrected complex orientation (antipodal composed with raw Hopf).
No continuity, smoothness, holomorphicity or contact matching is inferred. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorEquiv

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedAmbientEquiv
open CompactSymplecticProjectorAssociatedActualTwistorEquiv
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

def ambientActualTwistorEquiv
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
    ℙ ℂ (V n) ≃ TwistorSphere
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact (ambientAssociatedSphereEquiv n (standardRealQuaternionicStructure n q hq)).trans
    (associatedActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn)

theorem ambientActualTwistorEquiv_base
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (p : ℙ ℂ (V n)) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    projection (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn p) =
      twistorToCarrier n p := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact (associatedActualTwistorEquiv_base hLee hDesc hImm n d e q g a hq hn
      (ambientAssociatedSphereEquiv n (standardRealQuaternionicStructure n q hq) p)).trans
    (ambientAssociatedSphereEquiv_base n (standardRealQuaternionicStructure n q hq) p)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorEquiv
