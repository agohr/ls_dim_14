import QuaternionicSymmetry.ManifoldChartRefinementTangent

/-! Restricting the target's chart domains leaves the manifold derivative of
a differentiable map unchanged. Old/new target dictionaries are explicit. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementTargetDifferential

open Manifold
open ManifoldChartRefinement
open scoped Manifold ContDiff
noncomputable section

variable {E H M V K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace K] {J : ModelWithCorners ℝ V K}
  [TopologicalSpace N] [ChartedSpace K N]

theorem mfderiv_restrictedCharts_target_eq
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) (f : N → M) (x : N)
    (hf : MDifferentiableAt J I f x) :
    @mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
      E _ _ H _ I M _
      (restrictedCharts (H := H) W hWopen hWmem) f x =
    @mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
      E _ _ H _ I M _ (inferInstance : ChartedSpace H M) f x := by
  let oldCharts : ChartedSpace H M := inferInstance
  let newCharts : ChartedSpace H M := restrictedCharts (H := H) W hWopen hWmem
  have hOld : @HasMFDerivAt ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
      E _ _ H _ I M _ oldCharts f x
      (@mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
        E _ _ H _ I M _ oldCharts f x) :=
    @MDifferentiableAt.hasMFDerivAt ℝ _ V _ _ K _ J N _
      (inferInstance : ChartedSpace K N) E _ _ H _ I M _ oldCharts f x hf
  have hNew : @HasMFDerivAt ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
      E _ _ H _ I M _ newCharts f x
      (@mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
        E _ _ H _ I M _ oldCharts f x) := by
    simpa [HasMFDerivAt, writtenInExtChartAt, extChartAt,
      restrictedCharts, mfld_simps] using hOld
  exact @HasMFDerivAt.mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
    E _ _ H _ I M _ newCharts f x
    (@mfderiv ℝ _ V _ _ K _ J N _ (inferInstance : ChartedSpace K N)
      E _ _ H _ I M _ oldCharts f x) hNew

end
end QuaternionicSymmetry.ManifoldChartRefinementTargetDifferential
