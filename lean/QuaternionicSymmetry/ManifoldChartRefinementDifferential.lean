import QuaternionicSymmetry.ManifoldChartRefinementTangent

/-! Changing only the selected chart domains does not change the
actual manifold derivative of a differentiable map. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementDifferential

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

theorem mfderiv_restrictedCharts_eq
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) (f : M → N) (x : M)
    (hf : MDifferentiableAt I J f x) :
    @mfderiv ℝ _ E _ _ H _ I M _
      (restrictedCharts (H := H) W hWopen hWmem)
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x =
    @mfderiv ℝ _ E _ _ H _ I M _
      (inferInstance : ChartedSpace H M)
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x := by
  let oldCharts : ChartedSpace H M := inferInstance
  let newCharts : ChartedSpace H M := restrictedCharts (H := H) W hWopen hWmem
  have hOld : @HasMFDerivAt ℝ _ E _ _ H _ I M _ oldCharts
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x
      (@mfderiv ℝ _ E _ _ H _ I M _ oldCharts
        V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x) :=
    @MDifferentiableAt.hasMFDerivAt ℝ _ E _ _ H _ I M _ oldCharts
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x hf
  have hNew : @HasMFDerivAt ℝ _ E _ _ H _ I M _ newCharts
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x
      (@mfderiv ℝ _ E _ _ H _ I M _ oldCharts
        V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x) := by
    simpa [HasMFDerivAt, writtenInExtChartAt, extChartAt,
      restrictedCharts, mfld_simps] using hOld
  exact @HasMFDerivAt.mfderiv ℝ _ E _ _ H _ I M _ newCharts
    V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x
    (@mfderiv ℝ _ E _ _ H _ I M _ oldCharts
      V _ _ K _ J N _ (inferInstance : ChartedSpace K N) f x) hNew

end
end QuaternionicSymmetry.ManifoldChartRefinementDifferential
