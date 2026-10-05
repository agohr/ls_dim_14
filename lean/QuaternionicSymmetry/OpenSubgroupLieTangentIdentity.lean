import QuaternionicSymmetry.OpenSubgroupLie
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Tangent comparison for the genuine inherited atlas of an open subgroup.
This is the source-free bridge from identity-component Lie algebra to the
full group's Lie algebra used by the actual NT-C contact lift. -/

namespace QuaternionicSymmetry.OpenSubgroupLieTangentIdentity

open OpenSubgroupLie
open TopologicalSpace
open Filter Set
open scoped Manifold ContDiff Topology
noncomputable section

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace V G]
  (S : Subgroup G) (hS : IsOpen (S : Set G))

theorem mfderiv_inclusion_one_eq_id :
    letI := OpenSubgroupLie.charts (V := V) S hS
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (Subtype.val : S → G) 1 =
      ContinuousLinearMap.id ℝ V := by
  letI := OpenSubgroupLie.charts (V := V) S hS
  let U : Opens G := ⟨S,hS⟩
  let x : U := ⟨1,S.one_mem⟩
  change mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (Subtype.val : U → G) x = _
  have hrepr :
      writtenInExtChartAt 𝓘(ℝ,V) 𝓘(ℝ,V) x (Subtype.val : U → G)
        =ᶠ[𝓝 ((extChartAt 𝓘(ℝ,V) x) x)] id := by
    have hsymm := (U.chartAt_subtype_val_symm_eventuallyEq
      (H := V) (x := x)).fun_comp (chartAt V (1 : G))
    have hright := (chartAt V (1 : G)).eventually_right_inverse
      (mem_chart_target V (1 : G))
    simpa [writtenInExtChartAt, extChartAt] using hsymm.symm.trans hright
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have h := hasFDerivWithinAt_id (𝕜 := ℝ) ((extChartAt 𝓘(ℝ,V) x) x)
    (range 𝓘(ℝ,V))
  exact h.congr_of_eventuallyEq
    (hrepr.filter_mono (nhdsWithin_le_nhds)) hrepr.eq_of_nhds

end
end QuaternionicSymmetry.OpenSubgroupLieTangentIdentity
