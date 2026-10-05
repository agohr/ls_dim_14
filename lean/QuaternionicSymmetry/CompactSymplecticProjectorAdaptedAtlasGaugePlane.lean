import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan
import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasLocalSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! On every selected gauge neighborhood, one and the same actual local
representative provides C-infinity Euclidean generators and the exact
chart-coordinate image of the descended quaternionic tangent plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasGaugePlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorActualSmoothQuaternionicPlane
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasLocalSmooth
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem adaptedGauge_smooth_and_spans_actual_plane
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
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∃ σ : ProjectiveCarrier n → G n,
      (∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
          (euclideanLocalConjugateOperator n d e q g a σ x S)
          (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)) ∧
      ∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        ∃ C : RModel q ≃L[ℝ] RModel q,
          (C : RModel q →L[ℝ] RModel q) =
            tangentCoordChange 𝓘(ℝ, RModel q)
              (leftCosetAction n (σ y) (CompactSymplecticProjectorBaseTangent.baseCoset n))
              (leftCosetAction n (σ x) (CompactSymplecticProjectorBaseTangent.baseCoset n))
              (leftCosetAction n (σ y) (CompactSymplecticProjectorBaseTangent.baseCoset n)) ∧
          euclideanLocalFrameSpan hDesc hImm n d e q g a hq σ x y =
            ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
              ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
              (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨σ, _, hSmoothR, hSpan⟩ :=
    (Classical.choose_spec
      (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
        n d e q g a hq hn x)).2.2
  refine ⟨σ, ?_, ?_⟩
  · intro S
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    let W := actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x
    have hS := contMDiffOn_adaptedAtlas_of_original hLee hDesc hImm
      n d e q g a hq hn (localConjugateOperator n d e q g a σ x S) W
      (hSmoothR S)
    have hL : ContMDiffOn 𝓘(ℝ, EModel q)
        𝓘(ℝ, RModel q →L[ℝ] EModel q) ∞
        (fun _ : ProjectiveCarrier n =>
          (euclideanModelEquiv q).toContinuousLinearMap) W := contMDiffOn_const
    have hR : ContMDiffOn 𝓘(ℝ, EModel q)
        𝓘(ℝ, EModel q →L[ℝ] RModel q) ∞
        (fun _ : ProjectiveCarrier n =>
          (euclideanModelEquiv q).symm.toContinuousLinearMap) W := contMDiffOn_const
    exact (hL.clm_comp hS).clm_comp hR
  · intro y hy
    obtain ⟨C, hC, hPlane⟩ := hSpan y hy
    refine ⟨C, hC, ?_⟩
    rw [euclideanLocalFrameSpan_eq_original_map hDesc hImm
      n d e q g a hq σ x y, hPlane]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasGaugePlane
