import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDifferentialCocycle

/-! The differential cocycle as equality of actual tangent-space
continuous linear equivalences. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentCocycle

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorTranslationDifferentialCocycle
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem translationTangentEquiv_mul (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u v : G n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    (translationTangentEquiv n d e q g atlas (u * v) x).toLinearMap =
      ((translationTangentEquiv n d e q g atlas v x).trans
        (translationTangentEquiv n d e q g atlas u (leftCosetAction n v x))).toLinearMap := by
  letI := atlas.quotientCharts
  ext z
  exact congrArg (fun F : TangentSpace 𝓘(ℝ, RModel q) x →L[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n (u * v) x) => F z)
    (translation_mfderiv_mul n d e q g atlas u v x)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentCocycle
