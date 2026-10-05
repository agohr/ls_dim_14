import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDerivativeCenter
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth inversion, at each center of a genuine local gauge, of the
actual quotient-action tangent differential in fixed coordinates. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInverseSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorLocalDerivativeSmooth
open CompactSymplecticProjectorTranslationDerivativeCenter
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def gaugeDerivativeCoordinates
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ProjectiveCarrier n → (RModel q →L[ℝ] RModel q) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact (inTangentCoordinates 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
    (fun _ : G n => baseCoset n)
    (fun u : G n => leftCosetAction n u (baseCoset n))
    (fun u : G n => mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (leftCosetAction n u) (baseCoset n)) (σ x)) ∘ σ

theorem gaugeDerivativeCoordinates_inverse_smoothAt
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
      (fun y => ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x y)) x := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let T := translationTangentEquiv n d e q g a (σ x) (baseCoset n)
  let T' : RModel q ≃L[ℝ] RModel q := by
    exact T
  have hcenter : gaugeDerivativeCoordinates n d e q g a σ x x =
      (T' : RModel q →L[ℝ] RModel q) := by
    exact action_derivative_coordinates_center n d e q g a (σ x)
  have hInv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
      (gaugeDerivativeCoordinates n d e q g a σ x x) := by
    rw [hcenter]
    exact contDiffAt_map_inverse T'
  have hF := local_action_derivative_smoothAt n d e q g a U hU σ hσ x hx
  change ContMDiffAt 𝓘(ℝ, RModel q)
    𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
    (gaugeDerivativeCoordinates n d e q g a σ x) x at hF
  exact hInv.contMDiffAt.comp x hF

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInverseSmooth
