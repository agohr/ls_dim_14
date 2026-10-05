import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInverseSmooth

/-! The fixed-center gauge derivative is precisely the actual
translation differential followed by the genuine target tangent-chart
change. This is the bridge from smooth coordinate conjugates to Q(x). -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeCoordinateFormula

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem gaugeDerivativeCoordinates_eq_coordChange_comp
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    gaugeDerivativeCoordinates n d e q g a σ x y =
      (tangentCoordChange 𝓘(ℝ, RModel q)
        (leftCosetAction n (σ y) (baseCoset n))
        (leftCosetAction n (σ x) (baseCoset n))
        (leftCosetAction n (σ y) (baseCoset n))).comp
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y)) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hy
  change (inTangentCoordinates 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
    (fun _ : G n => baseCoset n)
    (fun u : G n => leftCosetAction n u (baseCoset n))
    (fun u : G n => mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (leftCosetAction n u) (baseCoset n)) (σ x)) (σ y) = _
  rw [inTangentCoordinates_eq (hx := by simp) (hy := hy)]
  apply ContinuousLinearMap.ext
  intro v
  change tangentCoordChange 𝓘(ℝ, RModel q)
      (leftCosetAction n (σ y) (baseCoset n))
      (leftCosetAction n (σ x) (baseCoset n))
      (leftCosetAction n (σ y) (baseCoset n))
      ((mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (σ y)) (baseCoset n))
        (tangentCoordChange 𝓘(ℝ, RModel q)
          (baseCoset n) (baseCoset n) (baseCoset n) v)) = _
  rw [tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, RModel q)) _)]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeCoordinateFormula
