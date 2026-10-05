import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeSmooth

/-! At its center, Mathlib's moving-target tangent-coordinate expression
is exactly the true differential of the actual quotient action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeCenter

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem action_derivative_coordinates_center
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (u₀ : G n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    (inTangentCoordinates 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (fun _ : G n => baseCoset n)
      (fun u : G n => leftCosetAction n u (baseCoset n))
      (fun u : G n => mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n u) (baseCoset n)) u₀) u₀ =
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n u₀) (baseCoset n) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  rw [inTangentCoordinates_eq (hx := by simp) (hy := by simp)]
  apply ContinuousLinearMap.ext
  intro v
  change tangentCoordChange 𝓘(ℝ, RModel q)
      (leftCosetAction n u₀ (baseCoset n))
      (leftCosetAction n u₀ (baseCoset n))
      (leftCosetAction n u₀ (baseCoset n))
      ((mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n u₀) (baseCoset n))
        (tangentCoordChange 𝓘(ℝ, RModel q)
          (baseCoset n) (baseCoset n) (baseCoset n) v)) = _
  rw [tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, RModel q)) _),
    tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, RModel q)) _)]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeCenter
