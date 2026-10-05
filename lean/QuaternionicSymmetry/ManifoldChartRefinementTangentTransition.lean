import QuaternionicSymmetry.ManifoldChartRefinementSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Preferred-chart tangent transitions are unchanged by restricting each
chart to an open neighborhood. The two ChartedSpace dictionaries are explicit. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementTangentTransition

open Manifold
open ManifoldChartRefinement
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem tangentCoordChange_restrictedCharts_eq
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x)
    (hNew : @IsManifold ℝ _ E _ _ H _ I 1 M _
      (restrictedCharts (H := H) W hWopen hWmem))
    (x y z : M) :
    (letI := restrictedCharts (H := H) W hWopen hWmem
     letI := hNew
     tangentCoordChange I x y z) = tangentCoordChange I x y z := by
  letI := restrictedCharts (H := H) W hWopen hWmem
  letI := hNew
  simp [tangentCoordChange, tangentBundleCore_coordChange,
    restrictedCharts, mfld_simps]
  rfl

end
end QuaternionicSymmetry.ManifoldChartRefinementTangentTransition
