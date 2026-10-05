import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSection
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeTransition
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan
import QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase

/-! On each strong chart the selected *smooth* quotient section also gives
smooth Euclidean I/J/K fields, with exact Q-span and core transition. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeFrame

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeSmoothTransport
open CompactSymplecticProjectorStrongGaugeTransition
open CompactSymplecticProjectorCosetActionBase
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem strongGaugeFrame_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (euclideanLocalConjugateOperator n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x S)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  let W := strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  rcases hSpec with ⟨_, _, _, _, _, _, hConjugate, _⟩
  have hOld : ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (localConjugateOperator n d e q g a σ x S) W :=
    (hConjugate S).mono Set.inter_subset_right
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  have hS := contMDiffOn_strongGauge_of_original hLee hDesc hImm
    n d e q g a hq hn (localConjugateOperator n d e q g a σ x S) W hOld
  have hL : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, RModel q →L[ℝ] EModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).toContinuousLinearMap) W := contMDiffOn_const
  have hR : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, EModel q →L[ℝ] RModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).symm.toContinuousLinearMap) W := contMDiffOn_const
  exact (hL.clm_comp hS).clm_comp hR

theorem strongGaugeFrame_span_and_core_at_points
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (strongEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    ∃ C : RModel q ≃L[ℝ] RModel q,
      euclideanLocalFrameSpan hDesc hImm n d e q g a hq
          (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y =
        ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
          ((C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
          (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) ∧
      (euclideanModelEquiv q).toContinuousLinearMap.comp
        ((C : RModel q →L[ℝ] RModel q).comp
          (euclideanModelEquiv q).symm.toContinuousLinearMap) =
        (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
          (achart (EModel q) y) (achart (EModel q) x) y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  rcases hSpec with ⟨_, _, _, _, _, _, _, hSpan⟩
  obtain ⟨C, hC, hPlane⟩ := hSpan y hy.2
  refine ⟨C, ?_, ?_⟩
  · rw [euclideanLocalFrameSpan_eq_original_map hDesc hImm
      n d e q g a hq σ x y]
    simpa [σ, strongGaugeSection] using
      congrArg (fun P : Submodule ℝ (Module.End ℝ (RModel q)) =>
        P.map (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap))
        hPlane
  · have hCore := strong_tangentCoordChange_eq_original_conj
      hLee hDesc hImm n d e q g a hq hn
      (leftCosetAction n (σ y) (baseCoset n))
      (leftCosetAction n (σ x) (baseCoset n))
      (leftCosetAction n (σ y) (baseCoset n))
    have hCore' : (euclideanModelEquiv q).toContinuousLinearMap.comp
        ((C : RModel q →L[ℝ] RModel q).comp
          (euclideanModelEquiv q).symm.toContinuousLinearMap) =
        tangentCoordChange 𝓘(ℝ, EModel q)
          (leftCosetAction n (σ y) (baseCoset n))
          (leftCosetAction n (σ x) (baseCoset n))
          (leftCosetAction n (σ y) (baseCoset n)) := by
      simpa only [hC] using hCore.symm
    have hx : x ∈ strongGaugeNeighborhood hLee hDesc hImm
        n d e q g a hq hn x :=
      mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x
    have hyσ : (σ y : ProjectiveCarrier n) = y :=
      strongGaugeSection_right_inverse hLee hDesc hImm
        n d e q g a hq hn x y hy
    have hxσ : (σ x : ProjectiveCarrier n) = x :=
      strongGaugeSection_right_inverse hLee hDesc hImm
        n d e q g a hq hn x x hx
    change (euclideanModelEquiv q).toContinuousLinearMap.comp
        ((C : RModel q →L[ℝ] RModel q).comp
          (euclideanModelEquiv q).symm.toContinuousLinearMap) =
        tangentCoordChange 𝓘(ℝ, EModel q) y x y
    simpa only [leftCosetAction_baseCoset, hyσ, hxσ]
      using hCore'

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeFrame
