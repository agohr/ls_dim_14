import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! The actual local Q-frame can be chosen together with a smooth
right-inverse section of the genuine quotient map on the same open set. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothSectionFrame

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorLocalQuaternionicGauge
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorFixedGaugeDerivativeSmooth
open CompactSymplecticProjectorLocalQuaternionicSmoothFrame
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorLocalQuaternionicPlaneChart
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualQuotientPlane_has_local_smooth_section_frame
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∃ W : Set (ProjectiveCarrier n), IsOpen W ∧ x ∈ W ∧
      ∃ σ : ProjectiveCarrier n → G n,
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ W ∧
        (∀ y ∈ W, (σ y : ProjectiveCarrier n) = y) ∧
        (∀ y ∈ W, leftCosetAction n (σ y)
          (CompactSymplecticProjectorBaseTangent.baseCoset n) ∈
          (chartAt (RModel q) (leftCosetAction n (σ x)
            (CompactSymplecticProjectorBaseTangent.baseCoset n))).source) ∧
        (∀ y ∈ W, ∃ E : RModel q ≃L[ℝ] RModel q,
          (E : RModel q →L[ℝ] RModel q) =
            gaugeDerivativeCoordinates n d e q g a σ x y) ∧
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
          (gaugeDerivativeCoordinates n d e q g a σ x) W ∧
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
          (fun y => ContinuousLinearMap.inverse
            (gaugeDerivativeCoordinates n d e q g a σ x y)) W ∧
        (∀ S : RModel q →L[ℝ] RModel q,
          ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
            (localConjugateOperator n d e q g a σ x S) W) ∧
        ∀ y ∈ W, ∃ C : RModel q ≃L[ℝ] RModel q,
          (C : RModel q →L[ℝ] RModel q) =
            tangentCoordChange 𝓘(ℝ, RModel q)
              (leftCosetAction n (σ y) (CompactSymplecticProjectorBaseTangent.baseCoset n))
              (leftCosetAction n (σ x) (CompactSymplecticProjectorBaseTangent.baseCoset n))
              (leftCosetAction n (σ y) (CompactSymplecticProjectorBaseTangent.baseCoset n)) ∧
          localFrameSpan hDesc hImm n d e q g a hq σ x y =
            (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
              ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨U, hUopen, hxU, σ, hσ, hright, _⟩ :=
    quotientImaginaryPlane_local_gauge hLee hDesc hImm n d e q g a hq hn x
  obtain ⟨W, hWopen, hxW, hWU, hOverlap, hInv, hSmooth⟩ :=
    localQuaternionicSmoothFrame n d e q g a U hUopen σ hσ x hxU
  have hDerivative : ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (gaugeDerivativeCoordinates n d e q g a σ x) W := by
    intro y hy
    exact (gaugeDerivativeCoordinates_smoothAt n d e q g a U hUopen σ hσ
      x y (hWU hy) (hOverlap y hy)).contMDiffWithinAt
  have hInverse : ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (fun y => ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x y)) W := by
    intro y hy
    obtain ⟨E, hE⟩ := hInv y hy
    have hInvAt : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x y) := by
      rw [← hE]
      exact contDiffAt_map_inverse E
    exact (hInvAt.contMDiffAt.comp y
      (hDerivative.contMDiffAt (hWopen.mem_nhds hy))).contMDiffWithinAt
  refine ⟨W, hWopen, hxW, σ, hσ.mono hWU,
    (fun y hy => hright y (hWU hy)), hOverlap, hInv,
    hDerivative, hInverse, hSmooth, ?_⟩
  intro y hy
  obtain ⟨E, hE⟩ := hInv y hy
  exact localFrameSpan_eq_charted_quotientImaginaryPlane hDesc hImm n d e q g a
    hq hn σ x y (hOverlap y hy) (hright y (hWU hy)) E hE

end
end QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothSectionFrame
