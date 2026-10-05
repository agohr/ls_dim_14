import QuaternionicSymmetry.CompactSymplecticProjectorLocalSection
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The true tangent differential of each checked quotient translation is
a continuous real-linear equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentEquiv

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticProjectorTranslationDiffeomorph
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Actual differential transport on tangent spaces, derived from the
smooth translation diffeomorphism with no model-geometry premise. -/
def translationTangentEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : G n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) x ≃L[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n u x) := by
  letI := atlas.quotientCharts
  exact (leftCosetDiffeomorph n d e q g atlas u).mfderivToContinuousLinearEquiv
    (by simp) x

@[simp] theorem translationTangentEquiv_apply
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : G n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      translationTangentEquiv n d e q g atlas u x v =
        mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) x v := by
  letI := atlas.quotientCharts
  intro v
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentEquiv
