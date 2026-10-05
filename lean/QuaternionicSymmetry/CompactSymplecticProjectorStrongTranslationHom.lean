import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicTranslation

/-! The actual compact symplectic group acts by quaternionic isometries of
the genuine strong-atlas HP tangent geometry, as a literal group map. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationHom

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTranslationDiffeomorph
open CompactSymplecticProjectorStrongQuaternionicTranslation
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorTranslationDiffeomorph
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicSpanSymmetry
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def translationQuaternionicIsometryHom
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    G n →* QuaternionicIsometries
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  refine {
    toFun := translationQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn
    map_one' := ?_
    map_mul' := ?_
  }
  · apply Subtype.ext
    apply Diffeomorph.ext
    intro x
    change leftCosetAction n (1 : G n) x = x
    exact leftCosetAction_one n x
  · intro u v
    apply Subtype.ext
    apply Diffeomorph.ext
    intro x
    change leftCosetAction n (u * v) x =
      leftCosetAction n u (leftCosetAction n v x)
    exact (leftCosetAction_mul n u v x).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationHom
