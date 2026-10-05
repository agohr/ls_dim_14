import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicGauge
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Smooth dependence of the true quotient-action differential on the
compact-symplectic element, expressed in the tangent coordinates
required by Mathlib's manifold derivative theorem. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- The derivative at the base projector of the actual group action
varies smoothly with its group parameter after the necessary moving
target tangent-coordinate conversion. -/
theorem action_derivative_smooth_in_tangent_coordinates
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (u₀ : G n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ContMDiffAt 𝓘(ℝ, RModel d)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (inTangentCoordinates 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (fun _ : G n => baseCoset n)
        (fun u : G n => leftCosetAction n u (baseCoset n))
        (fun u : G n => mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) (baseCoset n)) u₀) u₀ := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hf : ContMDiffAt (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q))
      𝓘(ℝ, RModel q) ∞
      (fun p : G n × ProjectiveCarrier n => leftCosetAction n p.1 p.2)
      (u₀, baseCoset n) := a.actionSmooth.contMDiffAt
  have hg : ContMDiffAt 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q) ∞
      (fun _ : G n => baseCoset n) u₀ := contMDiffAt_const
  exact hf.mfderiv (fun u y => leftCosetAction n u y)
    (fun _ : G n => baseCoset n) hg (by simp)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeSmooth
