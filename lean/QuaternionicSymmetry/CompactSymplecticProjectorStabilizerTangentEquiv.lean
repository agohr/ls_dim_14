import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDifferentialCocycle

/-! At the base coset, an actual stabilizer translation induces a
continuous linear automorphism of the true manifold tangent. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentEquiv

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStabilizerTangentFactor
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

def stabilizerTangentEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃L[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) := by
  letI := atlas.quotientCharts
  exact translationTangentEquiv n d e q g atlas u.1 (baseCoset n)

theorem stabilizerTangentEnd_injective
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    Function.Injective (stabilizerTangentEnd n d e q g atlas u) := by
  letI := atlas.quotientCharts
  intro v w hvw
  apply (translationTangentEquiv n d e q g atlas u.1 (baseCoset n)).injective
  exact hvw

theorem stabilizerTangentEquiv_toLinearMap
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    (stabilizerTangentEquiv n d e q g atlas u).toLinearMap =
      stabilizerTangentEnd n d e q g atlas u := by
  letI := atlas.quotientCharts
  ext v
  exact translationTangentEquiv_apply n d e q g atlas u.1 (baseCoset n) v

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentEquiv
