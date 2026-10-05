import QuaternionicSymmetry.ManifoldChartRefinement
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Restricting each preferred chart to an open neighborhood leaves
smoothness of maps out of the manifold unchanged, including on a subset. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementSmoothness

open Manifold
open ManifoldChartRefinement
open scoped Manifold ContDiff
noncomputable section

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

theorem contMDiffWithinAt_restrictedCharts_iff
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) (f : M → N) (s : Set M) (x : M) :
    (letI := restrictedCharts (H := H) W hWopen hWmem
     ContMDiffWithinAt I J ∞ f s x) ↔
      ContMDiffWithinAt I J ∞ f s x := by
  letI := restrictedCharts (H := H) W hWopen hWmem
  simp [contMDiffWithinAt_iff, extChartAt,
    restrictedCharts, mfld_simps]
  tauto

theorem contMDiffOn_restrictedCharts_iff
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) (f : M → N) (s : Set M) :
    (letI := restrictedCharts (H := H) W hWopen hWmem
     ContMDiffOn I J ∞ f s) ↔ ContMDiffOn I J ∞ f s := by
  simp only [ContMDiffOn]
  exact forall_congr' fun x => imp_congr_right fun _ =>
    contMDiffWithinAt_restrictedCharts_iff W hWopen hWmem f s x

end
end QuaternionicSymmetry.ManifoldChartRefinementSmoothness
