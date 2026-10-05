import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeCoordinateFormula
import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInvertible

/-! On a chart-overlap neighborhood, the invertible gauge derivative
factors through the actual tangent chart change. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicCoordinateBridge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalDerivativeCoordinateFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem gaugeDerivative_chartChange_equiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∃ C : RModel q ≃L[ℝ] RModel q,
        (C : RModel q →L[ℝ] RModel q) =
          tangentCoordChange 𝓘(ℝ, RModel q)
            (leftCosetAction n (σ y) (baseCoset n))
            (leftCosetAction n (σ x) (baseCoset n))
            (leftCosetAction n (σ y) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hy E hE
  let D : RModel q ≃L[ℝ] RModel q :=
    translationTangentEquiv n d e q g a (σ y) (baseCoset n)
  let C : RModel q ≃L[ℝ] RModel q := D.symm.trans E
  refine ⟨C, ?_⟩
  have hED : (E : RModel q →L[ℝ] RModel q) =
      (tangentCoordChange 𝓘(ℝ, RModel q)
        (leftCosetAction n (σ y) (baseCoset n))
        (leftCosetAction n (σ x) (baseCoset n))
        (leftCosetAction n (σ y) (baseCoset n))).comp
        (D : RModel q →L[ℝ] RModel q) := by
    exact hE.trans (gaugeDerivativeCoordinates_eq_coordChange_comp
      n d e q g a σ x y hy)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg
    (fun F : RModel q →L[ℝ] RModel q => F (D.symm v)) hED
  change E (D.symm v) =
    (tangentCoordChange 𝓘(ℝ, RModel q)
      (leftCosetAction n (σ y) (baseCoset n))
      (leftCosetAction n (σ x) (baseCoset n))
      (leftCosetAction n (σ y) (baseCoset n))) v
  calc
    E (D.symm v) =
        (tangentCoordChange 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y) (baseCoset n))
          (leftCosetAction n (σ x) (baseCoset n))
          (leftCosetAction n (σ y) (baseCoset n))) (D (D.symm v)) := by
      simpa only [ContinuousLinearMap.comp_apply] using hv
    _ = _ := by rw [D.apply_symm_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicCoordinateBridge
