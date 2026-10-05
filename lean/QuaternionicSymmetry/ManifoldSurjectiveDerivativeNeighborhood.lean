import QuaternionicSymmetry.ManifoldChartRelatedFields
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The local openness consequence of a surjective genuine manifold
derivative. The proof applies the internal Banach-space inverse-function
theorem in the actual source and target charts. -/

namespace QuaternionicSymmetry.ManifoldSurjectiveDerivativeNeighborhood

open ManifoldChartRelatedFields Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- The range of a smooth map contains a neighborhood of the image of
any point where its actual manifold derivative is surjective. -/
theorem range_mem_nhds_of_surjective_mfderiv
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (x : M) (hdf : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Set.range f ∈ 𝓝 (f x) := by
  let σ := extChartAt 𝓘(ℝ, E) x
  let τ := extChartAt 𝓘(ℝ, F) (f x)
  let c := chartMap (𝕜 := ℝ) (E := E) (F := F) f x
  have hc : HasStrictFDerivAt c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (σ x) := by
    have h := (chartMap_contDiffAt f hf x).hasStrictFDerivAt (by simp)
    rw [chartMap_fderiv_center f hf x] at h
    exact h
  have hmap : Filter.map c (𝓝 (σ x)) = 𝓝 (τ (f x)) := by
    have h := hc.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hdf)
    simpa only [c, σ, τ, chartMap_center] using h
  let U : Set E := σ.target ∩ σ.symm ⁻¹' (f ⁻¹' τ.source)
  have hσ : ContinuousAt σ.symm (σ x) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x _ (mem_extChartAt_target x)).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).continuousAt
  have hfx : ContinuousAt (f ∘ σ.symm) (σ x) := by
    apply hf.continuous.continuousAt.comp hσ
  have hU : U ∈ 𝓝 (σ x) := by
    apply inter_mem ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have h := hfx.preimage_mem_nhds
      (show τ.source ∈ 𝓝 ((f ∘ σ.symm) (σ x)) by
        simpa only [σ, τ, Function.comp_apply, extChartAt_to_inv] using
          extChartAt_source_mem_nhds (I := 𝓘(ℝ, F)) (f x))
    exact h
  have hcU : c '' U ∈ 𝓝 (τ (f x)) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  have hτmap : Filter.map τ.symm (𝓝 (τ (f x))) = 𝓝 (f x) := by
    simpa using map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, F)) (f x)
  have hout : τ.symm '' (c '' U) ∈ 𝓝 (f x) := by
    rw [← hτmap]
    exact Filter.image_mem_map hcU
  apply Filter.mem_of_superset hout
  rintro z ⟨v, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨σ.symm u, ?_⟩
  exact (τ.left_inv hu.2).symm

end

end QuaternionicSymmetry.ManifoldSurjectiveDerivativeNeighborhood
