import QuaternionicSymmetry.ComplexSmoothRealHessian

/-! The Cauchy–Riemann Hessian calculation localized to an open set.
Extended manifold chart maps are only differentiable on their chart overlap,
so global CR hypotheses would be too strong for the eventual application. -/

namespace QuaternionicSymmetry.ComplexSmoothRealHessianLocal

open Filter
open scoped Topology
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem real_hessian_commutes_i_inner_on
    {f : E → F} {s : Set E} (hs : IsOpen s)
    (hReal : ContDiffOn ℝ ∞ f s)
    (hComplex : DifferentiableOn ℂ f s)
    {x : E} (hx : x ∈ s) (v w : E) :
    (fderiv ℝ (fderiv ℝ f) x w) (Complex.I • v) =
      Complex.I • (fderiv ℝ (fderiv ℝ f) x w) v := by
  have hR : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hReal).2
      |>.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y : E => fderiv ℝ f y (Complex.I • v)) =ᶠ[𝓝 x]
      (fun y : E => Complex.I • fderiv ℝ f y v) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [((hComplex y hy).differentiableAt (hs.mem_nhds hy)).fderiv_restrictScalars ℝ]
    exact map_smul (fderiv ℂ f y) Complex.I v
  have hd : fderiv ℝ (fun y : E => fderiv ℝ f y (Complex.I • v)) x w =
      fderiv ℝ (fun y : E => Complex.I • fderiv ℝ f y v) x w := by
    exact congrArg (fun L : E →L[ℝ] F => L w) heq.fderiv_eq
  have hEval (u : E) :
      fderiv ℝ (fun y => fderiv ℝ f y u) x w =
        (fderiv ℝ (fderiv ℝ f) x w) u := by
    rw [fderiv_clm_apply hR (differentiableAt_const u)]
    simp
  have hEvalDiff : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    hR.clm_apply (differentiableAt_const v)
  change fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x w =
    fderiv ℝ (Complex.I • (fun y => fderiv ℝ f y v)) x w at hd
  rw [fderiv_const_smul hEvalDiff Complex.I] at hd
  simp only [ContinuousLinearMap.smul_apply] at hd
  rw [hEval v, hEval (Complex.I • v)] at hd
  exact hd

theorem real_hessian_commutes_i_outer_on
    {f : E → F} {s : Set E} (hs : IsOpen s)
    (hReal : ContDiffOn ℝ ∞ f s)
    (hComplex : DifferentiableOn ℂ f s)
    {x : E} (hx : x ∈ s) (v w : E) :
    (fderiv ℝ (fderiv ℝ f) x (Complex.I • w)) v =
      Complex.I • (fderiv ℝ (fderiv ℝ f) x w) v := by
  have hbound : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hsymm := ((hReal.contDiffAt (hs.mem_nhds hx)).isSymmSndFDerivAt hbound).eq
  rw [hsymm (Complex.I • w) v,
    real_hessian_commutes_i_inner_on hs hReal hComplex hx w v,
    hsymm v w]

end
end QuaternionicSymmetry.ComplexSmoothRealHessianLocal
