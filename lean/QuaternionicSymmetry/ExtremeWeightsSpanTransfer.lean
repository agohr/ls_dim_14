import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Internal convex step for geometric character separation. Once all
extreme fixed weights occur among section weights, full linear span passes
to the latter. Neither full span nor extremal nonvanishing is assumed to
follow merely from symmetry or ampleness. -/

namespace QuaternionicSymmetry.ExtremeWeightsSpanTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem span_eq_top_of_extremePoints_subset
    {K S : Set E} (hCompact : IsCompact K) (hConvex : Convex ℝ K)
    (hSpan : Submodule.span ℝ K = ⊤)
    (hExtreme : K.extremePoints ℝ ⊆ S) :
    Submodule.span ℝ S = ⊤ := by
  have hSub : K.extremePoints ℝ ⊆ (Submodule.span ℝ S : Set E) :=
    fun _ hx => Submodule.subset_span (hExtreme hx)
  have hHull : closure (convexHull ℝ (K.extremePoints ℝ)) ⊆
      (Submodule.span ℝ S : Set E) :=
    closure_minimal (convexHull_min hSub (Submodule.convex _))
      (Submodule.span ℝ S).closed_of_finiteDimensional
  rw [closure_convexHull_extremePoints hCompact hConvex] at hHull
  apply top_unique
  rw [← hSpan]
  exact Submodule.span_le.mpr hHull

theorem span_eq_top_of_finite_extremeWeights_subset
    {W S : Set E} (hFinite : W.Finite)
    (hSpan : Submodule.span ℝ W = ⊤)
    (hExtreme : (convexHull ℝ W).extremePoints ℝ ⊆ S) :
    Submodule.span ℝ S = ⊤ := by
  apply span_eq_top_of_extremePoints_subset hFinite.isCompact_convexHull
    (convex_convexHull ℝ W) ?_ hExtreme
  apply top_unique
  rw [← hSpan]
  exact Submodule.span_mono (subset_convexHull ℝ W)

end QuaternionicSymmetry.ExtremeWeightsSpanTransfer
