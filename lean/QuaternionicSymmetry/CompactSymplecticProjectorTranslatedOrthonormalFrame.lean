import QuaternionicSymmetry.CompactSymplecticProjectorBaseOrthonormalCoordinates
import QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentEquiv

/-! The explicit base Frobenius-orthonormal frame remains orthonormal
under every actual compact symplectic translation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslatedOrthonormalFrame

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def translatedOrthonormalFrame
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u : G n) :
    letI := a.quotientCharts
    EModel q ≃L[ℝ] TangentSpace 𝓘(ℝ, Fin q → ℝ)
      (leftCosetAction n u (baseCoset n)) := by
  letI := a.quotientCharts
  exact (baseOrthonormalFrame hDesc hImm n d e q g a hq).trans
    (translationTangentEquiv n d e q g a u (baseCoset n))

theorem translatedOrthonormalFrame_metric
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : EModel q,
      (smoothProjectorMetric hDesc hImm n d e q g a).inner
        (leftCosetAction n u (baseCoset n))
        (translatedOrthonormalFrame hDesc hImm n d e q g a hq u v)
        (translatedOrthonormalFrame hDesc hImm n d e q g a hq u w) =
      inner ℝ v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  change (smoothProjectorMetric hDesc hImm n d e q g a).inner
      (leftCosetAction n u (baseCoset n))
      (translationTangentEquiv n d e q g a u (baseCoset n)
        (baseOrthonormalFrame hDesc hImm n d e q g a hq v))
      (translationTangentEquiv n d e q g a u (baseCoset n)
        (baseOrthonormalFrame hDesc hImm n d e q g a hq w)) = _
  rw [translationTangentEquiv_apply, translationTangentEquiv_apply]
  rw [smoothProjectorMetric_invariant hDesc hImm n d e q g a u (baseCoset n)]
  exact baseOrthonormalFrame_metric hDesc hImm n d e q g a hq v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslatedOrthonormalFrame
