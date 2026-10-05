import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInverseSmooth

/-! Smooth local coordinate conjugates of every fixed base tangent
operator, built from the actual action derivative and its smooth inverse. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalDerivativeSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- In fixed tangent coordinates centered at `x`, conjugate a fixed
base-tangent operator by the true action derivative of the local gauge. -/
def localConjugateOperator
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x : ProjectiveCarrier n)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ProjectiveCarrier n → (RModel q →L[ℝ] RModel q) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact fun y => ((gaugeDerivativeCoordinates n d e q g a σ x y).comp S).comp
    (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y))

theorem localConjugateOperator_smoothAt
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x : ProjectiveCarrier n) (hx : x ∈ U)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ContMDiffAt 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (localConjugateOperator n d e q g a σ x S) x := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hA : ContMDiffAt 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (gaugeDerivativeCoordinates n d e q g a σ x) x := by
    exact local_action_derivative_smoothAt n d e q g a U hU σ hσ x hx
  have hS : ContMDiffAt 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (fun _ : ProjectiveCarrier n => S) x := contMDiffAt_const
  have hInv := gaugeDerivativeCoordinates_inverse_smoothAt n d e q g a U hU σ hσ x hx
  exact (hA.clm_comp hS).clm_comp hInv

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSmooth
