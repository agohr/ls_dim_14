import QuaternionicSymmetry.ManifoldChartRefinement
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Every index of a pointwise-restricted atlas has an actual center,
because that atlas is literally the range of the restricted preferred
charts. This choice lets local gauges be attached to arbitrary bundle-core
indices without changing the atlas again. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementCenter

open Manifold
open ManifoldChartRefinement
open scoped Manifold
noncomputable section

variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [old : ChartedSpace H M]
  (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
  (hWmem : ∀ x, x ∈ W x)

def center
    (i : @atlas H _ M _ (@restrictedCharts H M _ _ old W hWopen hWmem)) : M := by
  have hi : i.1 ∈ Set.range
      (fun x : M => (@chartAt H _ M _ old x).restr (W x)) := i.property
  exact Classical.choose hi

theorem chart_eq_restr
    (i : @atlas H _ M _ (@restrictedCharts H M _ _ old W hWopen hWmem)) :
    i.1 = (@chartAt H _ M _ old (center W hWopen hWmem i)).restr
      (W (center W hWopen hWmem i)) := by
  have hi : i.1 ∈ Set.range
      (fun x : M => (@chartAt H _ M _ old x).restr (W x)) := i.property
  exact (Classical.choose_spec hi).symm

theorem mem_neighborhood_of_mem_source
    (i : @atlas H _ M _ (@restrictedCharts H M _ _ old W hWopen hWmem))
    (y : M) (hy : y ∈ i.1.source) :
    y ∈ W (center W hWopen hWmem i) := by
  rw [chart_eq_restr W hWopen hWmem i,
    OpenPartialHomeomorph.restr_source' _ _
      (hWopen (center W hWopen hWmem i))] at hy
  exact hy.2

end
end QuaternionicSymmetry.ManifoldChartRefinementCenter
