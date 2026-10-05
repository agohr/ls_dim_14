import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSpan
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicCoordinateBridge
import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane

/-! The three smooth local coordinate-frame operators span exactly the
actual quotient quaternionic plane, expressed in the fixed chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicPlaneChart

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorLocalDerivativeCoordinateFormula
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorLocalQuaternionicCoordinateBridge
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

private theorem conjAlgEquiv_trans
    {V W X : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X]
    (A : V ≃ₗ[ℝ] W) (B : W ≃ₗ[ℝ] X) :
    (A.trans B).conjAlgEquiv ℝ =
      (A.conjAlgEquiv ℝ).trans (B.conjAlgEquiv ℝ) := by
  ext F v
  rfl

theorem localFrameSpan_eq_charted_quotientImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    leftCosetAction n (σ y) (baseCoset n) ∈
      (chartAt (RModel q) (leftCosetAction n (σ x) (baseCoset n))).source →
    (σ y : ProjectiveCarrier n) = y →
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∃ C : RModel q ≃L[ℝ] RModel q,
        (C : RModel q →L[ℝ] RModel q) =
          tangentCoordChange 𝓘(ℝ, RModel q)
            (leftCosetAction n (σ y) (baseCoset n))
            (leftCosetAction n (σ x) (baseCoset n))
            (leftCosetAction n (σ y) (baseCoset n)) ∧
        localFrameSpan hDesc hImm n d e q g a hq σ x y =
          (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
            ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro hy hσy E hE
  obtain ⟨C, hC⟩ := gaugeDerivative_chartChange_equiv n d e q g a σ x y hy E hE
  refine ⟨C, hC, ?_⟩
  let D := translationTangentEquiv n d e q g a (σ y) (baseCoset n)
  have hED : E.toLinearEquiv = D.toLinearEquiv.trans C.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun F : RModel q →L[ℝ] RModel q => F v)
      (hE.trans (gaugeDerivativeCoordinates_eq_coordChange_comp
        n d e q g a σ x y hy))
    simpa only [ContinuousLinearMap.comp_apply, ← hC] using hv
  rw [localFrameSpan_eq_map_baseImaginaryPlane hDesc hImm n d e q g a hq σ x y E hE]
  rw [← hσy]
  change (baseImaginaryPlane hDesc hImm n d e q g a hq).map
      ((E.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) =
    ((baseImaginaryPlane hDesc hImm n d e q g a hq).map
      ((D.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
      ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)
  rw [hED, conjAlgEquiv_trans]
  ext S
  constructor
  · rintro ⟨R, hR, hRS⟩
    exact ⟨(D.toLinearEquiv.conjAlgEquiv ℝ) R, ⟨R, hR, rfl⟩, hRS⟩
  · rintro ⟨R, ⟨R₀, hR₀, hRR⟩, hRS⟩
    exact ⟨R₀, hR₀, by rw [← hRR] at hRS; exact hRS⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicPlaneChart
