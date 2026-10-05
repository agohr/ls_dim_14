import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! The actual inclusion of an open subset into a manifold has identity
derivative in the inherited chart. -/

namespace QuaternionicSymmetry.OpenSubsetTangentIdentity

open TopologicalSpace Manifold Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {V G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace V G]
  [IsManifold 𝓘(ℝ,V) ∞ G]
  (U : Opens G) (x : U)

theorem subtype_mfderiv_eq_id :
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (Subtype.val : U → G) x =
      ContinuousLinearMap.id ℝ V := by
  have h : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V)
      (Subtype.val : U → G) x :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  rw [h.mfderiv]
  simp only [writtenInExtChartAt, mfld_simps]
  rw [fderivWithin_univ]
  have heq :
      (chartAt V (x : G) ∘ (Subtype.val : U → G) ∘
          (chartAt V x).symm) =ᶠ[𝓝 ((chartAt V x) x)]
        (id : V → V) := by
    have hsymm := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
      (H := V) U (x := x)).symm
    have htarget : (chartAt V (x : G)).target ∈
        𝓝 ((chartAt V x) x) := by
      apply (chartAt V (x : G)).open_target.mem_nhds
      exact (chartAt V (x : G)).map_source (mem_chart_source V (x : G))
    filter_upwards [hsymm, htarget] with y hy ht
    change (chartAt V (x : G))
      ((Subtype.val : U → G) ((chartAt V x).symm y)) = y
    have hy' : (Subtype.val : U → G) ((chartAt V x).symm y) =
        (chartAt V (x : G)).symm y := by
      simpa only [Function.comp_apply] using hy
    rw [hy']
    exact (chartAt V (x : G)).right_inv ht
  rw [heq.fderiv_eq]
  simp

end
end QuaternionicSymmetry.OpenSubsetTangentIdentity
