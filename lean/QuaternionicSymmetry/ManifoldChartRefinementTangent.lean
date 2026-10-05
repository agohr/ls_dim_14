import QuaternionicSymmetry.ManifoldChartRefinementDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Restricting chart domains leaves the coordinate differential of
the identity equal to the actual identity on the tangent model. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementTangent

open Manifold
open ManifoldChartRefinement
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem restrictedCharts_mfderiv_id
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) (x : M) :
    @mfderiv ℝ _ E _ _ H _ I M _
      (inferInstance : ChartedSpace H M)
      E _ _ H _ I M _
      (restrictedCharts (H := H) W hWopen hWmem)
      (id : M → M) x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  let oldCharts : ChartedSpace H M := inferInstance
  let newCharts : ChartedSpace H M := restrictedCharts (H := H) W hWopen hWmem
  have hOld : HasMFDerivAt I I (id : M → M) x
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) := hasMFDerivAt_id x
  have hNew : @HasMFDerivAt ℝ _ E _ _ H _ I M _ oldCharts
      E _ _ H _ I M _ newCharts (id : M → M) x
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
    simpa [HasMFDerivAt, writtenInExtChartAt, extChartAt,
      restrictedCharts, mfld_simps] using hOld
  exact @HasMFDerivAt.mfderiv ℝ _ E _ _ H _ I M _ oldCharts
    E _ _ H _ I M _ newCharts (id : M → M) x
    (ContinuousLinearMap.id ℝ (TangentSpace I x)) hNew

end
end QuaternionicSymmetry.ManifoldChartRefinementTangent
