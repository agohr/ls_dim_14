import QuaternionicSymmetry.GeneralSmoothMapSource
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Smoothness into an embedded finite-dimensional submanifold follows from
the inverse function theorem. A left inverse of the injective differential,
composed with the inclusion in charts, has identity derivative. Its smooth
local inverse recovers the original map from its ambient composite. -/

namespace QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib

open scoped Manifold ContDiff Topology
open Filter Function
noncomputable section

variable {E F V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An injective derivative permits local cancellation of a smooth outer
map, provided the inner map is continuous. -/
theorem contMDiffAt_of_comp_injective_fderiv
    {g : F → V} {f : M → F} {x : M}
    (hg : ContDiffAt ℝ ∞ g (f x))
    (hd : Function.Injective (fderiv ℝ g (f x)))
    (hf : ContinuousAt f x)
    (hgf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (g ∘ f) x) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x := by
  obtain ⟨L, hL⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hd
  have hcomp : L.comp (fderiv ℝ g (f x)) = ContinuousLinearMap.id ℝ F := by
    ext v
    exact hL v
  have hc : ContDiffAt ℝ ∞ (L ∘ g) (f x) := L.contDiff.contDiffAt.comp _ hg
  have hd' : HasFDerivAt (L ∘ g)
      (ContinuousLinearEquiv.refl ℝ F : F →L[ℝ] F) (f x) := by
    convert L.hasFDerivAt.comp (f x) (hg.differentiableAt (by simp)).hasFDerivAt using 1
    exact hcomp.symm
  have hinv := hc.to_localInverse hd' (by simp)
  have hsm := hinv.contMDiffAt.comp x (L.contDiff.contMDiff.contMDiffAt.comp x hgf)
  apply hsm.congr_of_eventuallyEq
  filter_upwards [hf.eventually
    ((hc.hasStrictFDerivAt' hd' (by simp)).eventually_left_inverse)] with y hy
  exact hy.symm

variable {N P : Type*}
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace P] [ChartedSpace V P]

/-- The pointwise manifold version only needs continuity of the map into
the submanifold and injectivity of the inclusion's derivative at its image. -/
theorem contMDiffAt_of_comp_injective_mfderiv
    {ι : N → P} {f : M → N} {x : M}
    (hι : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ ι (f x))
    (hd : Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι (f x)))
    (hf : ContinuousAt f x)
    (hιf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (ι ∘ f) x) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x := by
  let g := writtenInExtChartAt 𝓘(ℝ,F) 𝓘(ℝ,V) (f x) ι
  let k := extChartAt 𝓘(ℝ,F) (f x) ∘ f
  have hg : ContDiffAt ℝ ∞ g (k x) := by
    simpa [g, k] using (contMDiffAt_iff.mp hι).2
  have hgD : HasFDerivAt g (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι (f x)) (k x) := by
    simpa [g, k] using (hι.mdifferentiableAt (by simp)).hasMFDerivAt.2
  have hk : ContinuousAt k x := (continuousAt_extChartAt _).comp hf
  apply contMDiffAt_iff_target.mpr
  refine ⟨hf, contMDiffAt_of_comp_injective_fderiv hg ?_ hk ?_⟩
  · rwa [hgD.fderiv]
  · have hcoords := (contMDiffAt_iff_target.mp hιf).2
    apply hcoords.congr_of_eventuallyEq
    filter_upwards [hf.eventually (extChartAt_source_mem_nhds
      (I := 𝓘(ℝ,F)) (f x))] with y hy
    simp only [g, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt 𝓘(ℝ,F) (f x)).left_inv hy]

/-- The original BG-D3 contract, proved without a literature premise. -/
theorem embeddedCodomainRestriction :
    GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem := by
  intro E F V M N P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι f
    hEmbedding hι hd hιf x
  exact contMDiffAt_of_comp_injective_mfderiv (hι (f x)) (hd (f x))
    (hEmbedding.isInducing.continuousAt_iff.mpr (hιf x).continuousAt) (hιf x)

end
end QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib
