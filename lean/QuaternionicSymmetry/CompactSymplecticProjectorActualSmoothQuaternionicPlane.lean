import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicSmoothFrame
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicPlaneChart
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicGauge

/-! Actual local C-infinity frames for the descended rank-three
quaternionic tangent plane of the projector quotient. No Q-structure
or smoothness is supplied as a model premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorLocalQuaternionicGauge
open CompactSymplecticProjectorLocalQuaternionicSmoothFrame
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorLocalQuaternionicPlaneChart
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualQuotientPlane_has_local_smooth_frame
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
        (∀ y ∈ W, (σ y : ProjectiveCarrier n) = y) ∧
        (∀ S : RModel q →L[ℝ] RModel q,
          ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
            (localConjugateOperator n d e q g a σ x S) W) ∧
        ∀ y ∈ W, ∃ C : RModel q ≃L[ℝ] RModel q,
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
  obtain ⟨U, hUopen, hxU, σ, hσ, hright, _⟩ :=
    quotientImaginaryPlane_local_gauge hLee hDesc hImm n d e q g a hq hn x
  obtain ⟨W, hWopen, hxW, hWU, hOverlap, hInv, hSmooth⟩ :=
    localQuaternionicSmoothFrame n d e q g a U hUopen σ hσ x hxU
  refine ⟨W, hWopen, hxW, σ, (fun y hy => hright y (hWU hy)), hSmooth, ?_⟩
  intro y hy
  obtain ⟨E, hE⟩ := hInv y hy
  exact localFrameSpan_eq_charted_quotientImaginaryPlane hDesc hImm n d e q g a
    hq hn σ x y (hOverlap y hy) (hright y (hWU hy)) E hE

end
end QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane
