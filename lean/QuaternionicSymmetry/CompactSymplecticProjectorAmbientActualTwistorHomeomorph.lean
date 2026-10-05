import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientHomeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopfContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedActualTwistorHomeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorEquiv

/-! The SAME checked ambient CP^{2n+1} ↔ Levi-Civita twistor-sphere map
is a base-preserving homeomorphism. This is not yet a diffeomorphism or a
complex/contact identification. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorHomeomorph

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedAmbientHomeomorph
open CompactSymplecticProjectorAssociatedCorrectedEquiv
open CompactSymplecticProjectorAssociatedCorrectedHopfContinuous
open CompactSymplecticProjectorAssociatedActualTwistorHomeomorph
open CompactSymplecticProjectorAmbientActualTwistorEquiv
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereManifold
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

def associatedCorrectedHopfHomeomorph
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    AssociatedProjectiveFiber n ≃ₜ
      AssociatedSphereFiber n (standardRealQuaternionicStructure n q hq) := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI : CompactSpace (AssociatedProjectiveFiber n) := Quotient.compactSpace
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  letI : T2Space (TwistorSphere Q) := (sphereTotalHomeomorph Q).symm.isEmbedding.t2Space
  let H := associatedActualTwistorHomeomorph hR3 hLee hDesc hImm
    n d e q g a hq hn
  letI : T2Space (AssociatedSphereFiber n
      (standardRealQuaternionicStructure n q hq)) := H.isEmbedding.t2Space
  let E := associatedCorrectedHopfEquiv n
    (standardRealQuaternionicStructure n q hq)
  have hc : Continuous E := by
    change Continuous (CompactSymplecticProjectorAssociatedCorrectedHopf.associatedCorrectedHopf
      n (standardRealQuaternionicStructure n q hq))
    exact continuous_associatedCorrectedHopf n (standardRealQuaternionicStructure n q hq)
  exact E.toHomeomorphOfContinuousClosed hc hc.isClosedMap

def ambientActualTwistorHomeomorph
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
    ℙ ℂ (V n) ≃ₜ TwistorSphere
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact (associatedAmbientHomeomorph n).symm.trans
    ((associatedCorrectedHopfHomeomorph hR3 hLee hDesc hImm
      n d e q g a hq hn).trans
      (associatedActualTwistorHomeomorph hR3 hLee hDesc hImm
        n d e q g a hq hn))

theorem ambientActualTwistorHomeomorph_apply
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
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
    ambientActualTwistorHomeomorph hR3 hLee hDesc hImm n d e q g a hq hn p =
      ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn p := rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorHomeomorph
