import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorHomeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient

/-! Exact fiber formula for the actual CP-to-Levi-Civita-twistor
homeomorphism. The corrected Hopf antipodal sign is visible, and the Sp
action is the genuine derivative-induced action on the target. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorFiberFormula

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedToAmbient
open CompactSymplecticProjectorAssociatedAmbientEquiv
open CompactSymplecticProjectorAssociatedCorrectedHopf
open CompactSymplecticProjectorAssociatedCorrectedEquiv
open CompactSymplecticProjectorAssociatedActualTwistor
open CompactSymplecticProjectorAssociatedActualTwistorEquiv
open CompactSymplecticProjectorAmbientActualTwistorEquiv
open CompactSymplecticProjectorAmbientActualTwistorHomeomorph
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open FourDimensionalHalfSpinAntipodalVerticalSign
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinProjective
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem ambientActualTwistorEquiv_fiber
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (u : G n) (p : ProjectiveSpinor) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
    ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
      (fiberProjectiveLine n (firstColumnSphere n u) p) =
      u • strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn
        (antipodalCoefficient (projectiveHopf p)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := projectiveFiberAction n
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  have hline : (associatedAmbientEquiv n).symm
      (fiberProjectiveLine n (firstColumnSphere n u) p) =
      (⟦(u,p)⟧ : AssociatedProjectiveFiber n) := by
    apply (associatedAmbientEquiv n).injective
    rw [(associatedAmbientEquiv n).apply_symm_apply]
    rfl
  change associatedSphereToActualTwistor hLee hDesc hImm n d e q g a hq hn
    (associatedCorrectedHopfEquiv n (standardRealQuaternionicStructure n q hq)
      ((associatedAmbientEquiv n).symm
        (fiberProjectiveLine n (firstColumnSphere n u) p))) = _
  rw [hline, associatedCorrectedHopfEquiv_apply,
    associatedCorrectedHopf_mk, associatedSphereToActualTwistor_mk]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorFiberFormula
