import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeSmooth

/-! Smoothness of the true quotient-action derivative along any smooth
local representative gauge, in fixed tangent coordinates at a center. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationDerivativeSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem local_action_derivative_smoothAt
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x : ProjectiveCarrier n) (hx : x ∈ U) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      ((inTangentCoordinates 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (fun _ : G n => baseCoset n)
        (fun u : G n => leftCosetAction n u (baseCoset n))
        (fun u : G n => mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) (baseCoset n)) (σ x)) ∘ σ) x := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact (action_derivative_smooth_in_tangent_coordinates n d e q g a (σ x)).comp x
    (hσ.contMDiffAt (hU.mem_nhds hx))

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeSmooth
