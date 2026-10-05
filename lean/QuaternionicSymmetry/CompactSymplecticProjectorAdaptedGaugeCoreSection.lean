import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCorePackage
import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasLocalSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! Keep the actual quotient right inverse, smooth Euclidean Q generators,
exact Q-span, and refined tangent-core transition for one and the same σ. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreSection

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorActualSmoothQuaternionicPlane
open CompactSymplecticProjectorAdaptedAtlasLocalSmooth
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedGaugeCoreTransition
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actualGauge_section_smooth_span_and_core_transition
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
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (adaptedEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    ∃ σ : ProjectiveCarrier n → G n,
      (∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        (σ y : ProjectiveCarrier n) = y) ∧
      (∀ S : RModel q →L[ℝ] RModel q,
        ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
          (euclideanLocalConjugateOperator n d e q g a σ x S)
          (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)) ∧
      ∀ y ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
        ∃ C : RModel q ≃L[ℝ] RModel q,
          euclideanLocalFrameSpan hDesc hImm n d e q g a hq σ x y =
            ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
              ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
              (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) ∧
          (euclideanModelEquiv q).toContinuousLinearMap.comp
            ((C : RModel q →L[ℝ] RModel q).comp
              (euclideanModelEquiv q).symm.toContinuousLinearMap) =
            (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
              (achart (EModel q) (leftCosetAction n (σ y) (baseCoset n)))
              (achart (EModel q) (leftCosetAction n (σ x) (baseCoset n)))
              (leftCosetAction n (σ y) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨σ, hRight, hSmoothR, hSpan⟩ :=
    (Classical.choose_spec
      (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
        n d e q g a hq hn x)).2.2
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  refine ⟨σ, hRight, ?_, ?_⟩
  · intro S
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
    refine ⟨C, ?_, ?_⟩
    · rw [euclideanLocalFrameSpan_eq_original_map hDesc hImm
        n d e q g a hq σ x y, hPlane]
    · exact localChartChange_eq_adaptedTangentCore hLee hDesc hImm
        n d e q g a hq hn σ x y C hC

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreSection
