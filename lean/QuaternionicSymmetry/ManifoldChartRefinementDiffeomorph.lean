import QuaternionicSymmetry.ManifoldChartRefinement
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The original and pointwise-restricted smooth chart atlases have
the same smooth structure, witnessed by an actual identity diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldChartRefinementDiffeomorph

open Manifold
open ManifoldChartRefinement
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def restrictedChartsDiffeomorph
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) :
    @Diffeomorph ℝ _ E _ _ E _ _ H _ H _ I I M _
      (inferInstance : ChartedSpace H M) M _
      (restrictedCharts (H := H) W hWopen hWmem) ∞ := by
  let oldCharts : ChartedSpace H M := inferInstance
  let newCharts : ChartedSpace H M := restrictedCharts (H := H) W hWopen hWmem
  have hOld (x : M) : ContMDiffAt I I ∞ (id : M → M) x := contMDiffAt_id
  refine @Diffeomorph.mk ℝ _ E _ _ E _ _ H _ H _ I I M _
    oldCharts M _ newCharts ∞ (Equiv.refl M) ?_ ?_
  · intro x
    change @ContMDiffAt ℝ _ E _ _ H _ I M _ oldCharts
      E _ _ H _ I M _ newCharts ∞ (id : M → M) x
    rw [@contMDiffAt_iff ℝ _ E _ _ H _ I M _ oldCharts
      E _ _ H _ I M _ newCharts ∞ (id : M → M) x]
    simpa [extChartAt, restrictedCharts, mfld_simps] using
      (contMDiffAt_iff.mp (hOld x))
  · intro x
    change @ContMDiffAt ℝ _ E _ _ H _ I M _ newCharts
      E _ _ H _ I M _ oldCharts ∞ (id : M → M) x
    rw [@contMDiffAt_iff ℝ _ E _ _ H _ I M _ newCharts
      E _ _ H _ I M _ oldCharts ∞ (id : M → M) x]
    simpa [extChartAt, restrictedCharts, mfld_simps] using
      (contMDiffAt_iff.mp (hOld x))

end
end QuaternionicSymmetry.ManifoldChartRefinementDiffeomorph
