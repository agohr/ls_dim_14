import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicConjugationBridge
import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicSpan

/-! Exact local coordinate-frame image of the checked base
quaternionic generators under an invertible gauge derivative. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicOperatorImage

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localConjugateOperator_toLinearMap
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ (E : RModel q ≃L[ℝ] RModel q),
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∀ (S : RModel q →L[ℝ] RModel q),
        (localConjugateOperator n d e q g a σ x S y).toLinearMap =
          (E.toLinearEquiv.conjAlgEquiv ℝ) S.toLinearMap := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro E hE S
  apply LinearMap.ext
  intro v
  change ((gaugeDerivativeCoordinates n d e q g a σ x y).comp S).comp
    (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) v = _
  rw [← hE, ContinuousLinearMap.inverse_equiv]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicOperatorImage
