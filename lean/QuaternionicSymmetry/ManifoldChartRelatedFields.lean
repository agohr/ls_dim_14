import QuaternionicSymmetry.ManifoldChartVectorField

/-! A map and related tangent fields in fixed manifold charts. All
identities are on the genuine chart domains; off-chart extensions are
never assumed to satisfy the chain rule. -/

namespace QuaternionicSymmetry.ManifoldChartRelatedFields

open ManifoldChartVectorField VectorField
open scoped Manifold ContDiff Topology
noncomputable section

variable {𝕜 E F M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(𝕜,F) ∞ N]

theorem chartField_apply_of_mem_target
    (V : (x : M) → TangentSpace 𝓘(𝕜,E) x) (x : M)
    {y : E} (hy : y ∈ (extChartAt 𝓘(𝕜,E) x).target) :
    chartField V x y =
      mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x)
        ((extChartAt 𝓘(𝕜,E) x).symm y)
        (V ((extChartAt 𝓘(𝕜,E) x).symm y)) := by
  have hleft := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy
  have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy
  rw [show Set.range 𝓘(𝕜,E) = Set.univ by simp] at hleft hright
  have hinv := ContinuousLinearMap.inverse_eq hright hleft
  simp only [chartField, mpullbackWithin_apply]
  rw [hinv]
  rfl

def chartMap (f : M → N) (x : M) : E → F :=
  (extChartAt 𝓘(𝕜,F) (f x)) ∘ f ∘ (extChartAt 𝓘(𝕜,E) x).symm

theorem chartMap_center (f : M → N) (x : M) :
    chartMap (𝕜 := 𝕜) (E := E) (F := F) f x (extChartAt 𝓘(𝕜,E) x x) =
      extChartAt 𝓘(𝕜,F) (f x) (f x) := by
  unfold chartMap
  simp only [Function.comp_apply, extChartAt_to_inv]

theorem chartMap_contDiffAt (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f) (x : M) :
    ContDiffAt 𝕜 ∞ (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x)
      (extChartAt 𝓘(𝕜,E) x x) := by
  have hσ : ContMDiffAt 𝓘(𝕜,E) 𝓘(𝕜,E) ∞
      (extChartAt 𝓘(𝕜,E) x).symm (extChartAt 𝓘(𝕜,E) x x) :=
    (contMDiffOn_extChartAt_symm x _ (mem_extChartAt_target x)).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hfx := (hf.contMDiffAt (x := x)).comp_of_eq hσ (extChartAt_to_inv x)
  have hτ : ContMDiffAt 𝓘(𝕜,F) 𝓘(𝕜,F) ∞
      (extChartAt 𝓘(𝕜,F) (f x)) (f x) := contMDiffAt_extChartAt
  have h := hτ.comp_of_eq hfx (by simp [Function.comp_def])
  exact contMDiffAt_iff_contDiffAt.mp h

theorem chartMap_fderiv (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f) (x : M)
    {y : E} (hy : y ∈ (extChartAt 𝓘(𝕜,E) x).target)
    (hfy : f ((extChartAt 𝓘(𝕜,E) x).symm y) ∈
      (extChartAt 𝓘(𝕜,F) (f x)).source) :
    fderiv 𝕜 (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x) y =
      (mfderiv 𝓘(𝕜,F) 𝓘(𝕜,F) (extChartAt 𝓘(𝕜,F) (f x))
        (f ((extChartAt 𝓘(𝕜,E) x).symm y))).comp
        ((mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f ((extChartAt 𝓘(𝕜,E) x).symm y)).comp
          (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x).symm y)) := by
  have hσ : MDifferentiableAt 𝓘(𝕜,E) 𝓘(𝕜,E)
      (extChartAt 𝓘(𝕜,E) x).symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x y hy).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hy)).mdifferentiableAt (by simp)
  have hτ : MDifferentiableAt 𝓘(𝕜,F) 𝓘(𝕜,F)
      (extChartAt 𝓘(𝕜,F) (f x)) (f ((extChartAt 𝓘(𝕜,E) x).symm y)) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hfy)
  have hdf := hf.mdifferentiableAt (by simp) (x := (extChartAt 𝓘(𝕜,E) x).symm y)
  rw [← mfderiv_eq_fderiv]
  unfold chartMap
  rw [mfderiv_comp y hτ (hdf.comp y hσ), mfderiv_comp y hdf hσ]
  rfl

theorem chartMap_fderiv_center (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f) (x : M) :
    fderiv 𝕜 (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x)
      (extChartAt 𝓘(𝕜,E) x x) =
      mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f x := by
  rw [chartMap_fderiv f hf x (mem_extChartAt_target x)
    (by simpa only [extChartAt_to_inv] using mem_extChartAt_source (I := 𝓘(𝕜,F)) (f x)),
    extChartAt_to_inv, chart_mfderiv_center, chart_symm_mfderiv_center]
  ext v
  rfl

end
end QuaternionicSymmetry.ManifoldChartRelatedFields
