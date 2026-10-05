import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationHom
import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction

/-! The actual compact symplectic group acts on the already constructed
strong-atlas quaternionic twistor sphere through genuine derivative-induced
quaternionic isometries. This is not merely an abstract associated action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorAction

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTranslationHom
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongTranslationDiffeomorph
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def strongTwistorAction
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
    MulAction (G n)
      (TwistorSphere (strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let ρ := translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn
  letI : MulAction (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries Q)
      (TwistorSphere Q) := inferInstance
  exact MulAction.compHom (TwistorSphere Q) ρ

theorem strongTwistorAction_projection
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
    ∀ (z : TwistorSphere (strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn)),
    projection (strongQuaternionicHermitianTangent hLee hDesc hImm
      n d e q g a hq hn) (u • z) =
      leftCosetAction n u
        (projection (strongQuaternionicHermitianTangent hLee hDesc hImm
          n d e q g a hq hn) z) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  intro z
  change projection Q (twistorMap Q
    ((translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn) u) z) = _
  rw [projection_twistorMap]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorAction
