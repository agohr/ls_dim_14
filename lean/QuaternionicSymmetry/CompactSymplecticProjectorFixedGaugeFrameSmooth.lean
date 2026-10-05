import QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeDerivativeSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSmooth

/-! All-orders smoothness at every point of a fixed quaternionic
coordinate gauge on which the actual action derivative is invertible. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeFrameSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorFixedGaugeDerivativeSmooth
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localConjugateOperator_smoothAt_of_overlap
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x y : ProjectiveCarrier n) (hy : y ∈ U)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    (∃ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y) →
    ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (localConjugateOperator n d e q g a σ x S) y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hxy ⟨E, hE⟩
  have hA := gaugeDerivativeCoordinates_smoothAt n d e q g a U hU σ hσ x y hy hxy
  have hInv : ContMDiffAt 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (fun z => ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x z)) y := by
    have hInvAt : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x y) := by
      rw [← hE]
      exact contDiffAt_map_inverse E
    exact hInvAt.contMDiffAt.comp y hA
  have hS : ContMDiffAt 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (fun _ : ProjectiveCarrier n => S) y := contMDiffAt_const
  exact (hA.clm_comp hS).clm_comp hInv

end
end QuaternionicSymmetry.CompactSymplecticProjectorFixedGaugeFrameSmooth
