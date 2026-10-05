import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInverseSmooth
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! The actual quotient-action derivative stays invertible on a
neighborhood in each smooth local representative gauge. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInvertible

open Manifold Set Filter
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorLocalDerivativeSmooth
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorTranslationDerivativeCenter
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem gaugeDerivativeCoordinates_locally_invertible
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x : ProjectiveCarrier n) (hx : x ∈ U) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∃ V : Set (ProjectiveCarrier n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, ∃ T : RModel q ≃L[ℝ] RModel q,
        (T : RModel q →L[ℝ] RModel q) =
          gaugeDerivativeCoordinates n d e q g a σ x y := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let F := gaugeDerivativeCoordinates n d e q g a σ x
  let T : RModel q ≃L[ℝ] RModel q :=
    translationTangentEquiv n d e q g a (σ x) (baseCoset n)
  have hcenter : F x = (T : RModel q →L[ℝ] RModel q) :=
    action_derivative_coordinates_center n d e q g a (σ x)
  have hFx : F x ∈ Set.range ((↑) : (RModel q ≃L[ℝ] RModel q) →
      RModel q →L[ℝ] RModel q) := by
    exact ⟨T, hcenter.symm⟩
  have hF : ContinuousAt F x :=
    (local_action_derivative_smoothAt n d e q g a U hU σ hσ x hx).continuousAt
  have hV : F ⁻¹' Set.range ((↑) : (RModel q ≃L[ℝ] RModel q) →
      RModel q →L[ℝ] RModel q) ∈ 𝓝 x :=
    hF.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hFx)
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) hV)
  refine ⟨V, hVopen, hxV, ?_, ?_⟩
  · exact fun y hy => (hVU hy).1
  · intro y hy
    exact (hVU hy).2

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInvertible
