import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicCoordinateBridge
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSmooth

/-! The smooth local coordinate conjugate is exactly the actual
transported tangent operator expressed through the verified tangent
chart-change equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicConjugationBridge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalDerivativeCoordinateFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localConjugateOperator_eq_chart_transport
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    ∀ (E C D : RModel q ≃L[ℝ] RModel q),
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      (C : RModel q →L[ℝ] RModel q) =
        tangentCoordChange 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y) (baseCoset n))
          (leftCosetAction n (σ x) (baseCoset n))
          (leftCosetAction n (σ y) (baseCoset n)) →
      (D : RModel q →L[ℝ] RModel q) =
        mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y)) (baseCoset n) →
      ∀ S : RModel q →L[ℝ] RModel q,
        localConjugateOperator n d e q g a σ x S y =
          ((C : RModel q →L[ℝ] RModel q).comp
            ((D : RModel q →L[ℝ] RModel q).comp
              (S.comp (D.symm : RModel q →L[ℝ] RModel q)))).comp
            (C.symm : RModel q →L[ℝ] RModel q) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hy E C D hE hC hD S
  have hED : E = D.trans C := by
    apply ContinuousLinearEquiv.ext
    funext v
    have hA : (E : RModel q →L[ℝ] RModel q) =
        (C : RModel q →L[ℝ] RModel q).comp
          (D : RModel q →L[ℝ] RModel q) := by
      calc
        _ = gaugeDerivativeCoordinates n d e q g a σ x y := hE
        _ = (tangentCoordChange 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y) (baseCoset n))
          (leftCosetAction n (σ x) (baseCoset n))
          (leftCosetAction n (σ y) (baseCoset n))).comp
          (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
            (leftCosetAction n (σ y)) (baseCoset n)) :=
          gaugeDerivativeCoordinates_eq_coordChange_comp n d e q g a σ x y hy
        _ = _ := by rw [← hC, ← hD]
    have hv := congrArg (fun F : RModel q →L[ℝ] RModel q => F v)
      hA
    exact hv
  change ((gaugeDerivativeCoordinates n d e q g a σ x y).comp S).comp
      (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) = _
  rw [← hE, hED, ContinuousLinearMap.inverse_equiv]
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.comp_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicConjugationBridge
