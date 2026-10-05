import QuaternionicSymmetry.ComplexParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! A continuously varying complex derivative differentiates a compact
real parameter integral and makes that integral continuously differentiable. -/
namespace QuaternionicSymmetry.ComplexParametricIntegralC1
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 800000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuity of a fixed-interval integral on an open parameter domain. -/
theorem integral_continuousOn {U : Set E} (F : E → ℝ → F)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ)) (a b : ℝ) :
    ContinuousOn (fun x => ∫ t in a..b, F x t) U := by
  rw [continuousOn_iff_continuous_restrict]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply hF.comp_continuous
    (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
  exact fun p => ⟨p.1.2,Set.mem_univ _⟩

theorem integral_contDiffOn_one {U : Set E} (hU : IsOpen U)
    (f : E → ℝ → F) (d : E → ℝ → E →L[ℂ] F)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Set.univ))
    (hd : ContinuousOn (Function.uncurry d) (U ×ˢ Set.univ))
    (hder : ∀ x ∈ U, ∀ t, HasFDerivAt (fun y => f y t) (d x t) x) (a b : ℝ) :
    ContDiffOn ℂ 1 (fun x => ∫ t in a..b, f x t) U := by
  have hD (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ t in a..b, f y t) (∫ t in a..b, d x t) x := by
    letI : ProperSpace E := FiniteDimensional.proper ℂ E
    obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let K := closedBall x (δ/2)
    have hKU : K ⊆ U := (closedBall_subset_ball (half_lt_self hδ)).trans hsub
    have hK : IsCompact K := isCompact_closedBall x (δ/2)
    have hdc : ContinuousOn (fun p : E × ℝ => ‖d p.1 p.2‖) (K ×ˢ uIcc a b) :=
      hd.norm.mono (Set.prod_mono hKU (Set.subset_univ _))
    obtain ⟨B,hB⟩ := (hK.prod isCompact_uIcc).bddAbove_image hdc
    apply ComplexParametricIntervalIntegral.hasFDerivAt_intervalIntegral_of_continuous
      (s := K) (B := B) (closedBall_mem_nhds x (by positivity))
    · intro y hy
      exact hf.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t _ => ⟨hKU hy,Set.mem_univ t⟩)
    · exact hd.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t _ => ⟨hx,Set.mem_univ t⟩)
    · intro t ht y hy
      exact hB (Set.mem_image_of_mem (fun p : E × ℝ => ‖d p.1 p.2‖)
        (show (y,t) ∈ K ×ˢ uIcc a b from ⟨hy,ht⟩))
    · intro t _ y hy
      exact hder y (hKU hy) t
  have hh : ContDiffOn ℂ (0+1) (fun x => ∫ t in a..b, f x t) U := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
    refine ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    apply contDiffOn_zero.mpr
    apply (integral_continuousOn d hd a b).congr
    intro x hx
    exact (hD x hx).fderiv
  simpa using hh

end
end QuaternionicSymmetry.ComplexParametricIntegralC1
