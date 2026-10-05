import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeInvertible
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSmooth

/-! For each fixed finite differentiability order, a possibly
order-dependent open neighborhood supports that regularity for a
transported base-tangent operator, while the action derivative stays
invertible. A common all-orders domain is a separate obligation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalSmoothFrameNeighborhood

open Manifold Set Filter
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorLocalDerivativeInvertible
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localConjugateOperator_smoothNeighborhood
    (n d e q m : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (U : Set (ProjectiveCarrier n)) (hU : IsOpen U)
    (σ : ProjectiveCarrier n → G n)
    (hσ : letI := g.charts; letI := a.quotientCharts;
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U)
    (x : ProjectiveCarrier n) (hx : x ∈ U)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∃ V : Set (ProjectiveCarrier n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      (∀ y ∈ V, ∃ T : RModel q ≃L[ℝ] RModel q,
        (T : RModel q →L[ℝ] RModel q) =
          gaugeDerivativeCoordinates n d e q g a σ x y) ∧
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q →L[ℝ] RModel q) m
        (localConjugateOperator n d e q g a σ x S) V := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : IsManifold 𝓘(ℝ, RModel q) m (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by norm_cast; exact le_top)
  obtain ⟨V₁, hV₁, hxV₁, hV₁U, hInv⟩ :=
    gaugeDerivativeCoordinates_locally_invertible n d e q g a U hU σ hσ x hx
  have hAt := (localConjugateOperator_smoothAt n d e q g a U hU σ hσ x hx S).of_le
    (by norm_cast; exact le_top : (m : WithTop ℕ∞) ≤ ∞)
  obtain ⟨V₂, hV₂nhds, hSmooth₂⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := 𝓘(ℝ, RModel q))
      (I' := 𝓘(ℝ, RModel q →L[ℝ] RModel q))
      (n := (m : WithTop ℕ∞)) (by simp)).mp hAt
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp
    (inter_mem (hV₁.mem_nhds hxV₁) hV₂nhds)
  refine ⟨V, hV, hxV, (fun y hy => hV₁U (hVsub hy).1),
    (fun y hy => hInv y (hVsub hy).1), hSmooth₂.mono ?_⟩
  exact fun y hy => (hVsub hy).2

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalSmoothFrameNeighborhood
