import QuaternionicSymmetry.CompactSymplecticProjectorTranslatedImaginaryPlane

/-! The true manifold differentials of actual quotient translations obey
the group-action cocycle law. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationDifferentialCocycle

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticProjectorTranslationDiffeomorph
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- The exact differential cocycle for actual smooth left translations. -/
theorem translation_mfderiv_mul (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u v : G n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (leftCosetAction n (u * v)) x =
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n u) (leftCosetAction n v x)).comp
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n v) x) := by
  letI := atlas.quotientCharts
  have heq : leftCosetAction n (u * v) =
      (leftCosetAction n u) ∘ (leftCosetAction n v) := by
    funext y
    exact (leftCosetAction_mul n u v y).symm
  rw [heq]
  exact mfderiv_comp x
    ((leftCosetAction_smooth n d e q g atlas u).mdifferentiableAt (by simp))
    ((leftCosetAction_smooth n d e q g atlas v).mdifferentiableAt (by simp))

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationDifferentialCocycle
