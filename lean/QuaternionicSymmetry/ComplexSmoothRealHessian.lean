import QuaternionicSymmetry.ComplexSmoothRealBridge
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Differentiating the Cauchy–Riemann equation of a real-smooth
complex-differentiable map. This is the algebraic core of the higher-order
complex smoothness upgrade. -/

namespace QuaternionicSymmetry.ComplexSmoothRealHessian

open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem real_fderiv_commutes_i
    {f : E → F} (hComplex : Differentiable ℂ f)
    (x : E) (v : E) :
    fderiv ℝ f x (Complex.I • v) =
      Complex.I • fderiv ℝ f x v := by
  rw [(hComplex x).fderiv_restrictScalars ℝ]
  exact map_smul (fderiv ℂ f x) Complex.I v

/-- The real Hessian of a complex-differentiable map is complex-linear in
its inner argument, obtained by differentiating the pointwise CR identity. -/
theorem real_hessian_commutes_i_inner
    {f : E → F} (hReal : ContDiff ℝ ∞ f)
    (hComplex : Differentiable ℂ f)
    (x v w : E) :
    (fderiv ℝ (fderiv ℝ f) x w) (Complex.I • v) =
      Complex.I • (fderiv ℝ (fderiv ℝ f) x w) v := by
  have hR : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((contDiff_infty_iff_fderiv.mp hReal).2).differentiable (by simp) x
  have heq : (fun y : E => fderiv ℝ f y (Complex.I • v)) =
      (fun y : E => Complex.I • fderiv ℝ f y v) := by
    funext y
    exact real_fderiv_commutes_i hComplex y v
  have hd := congrArg (fun g : E → F => fderiv ℝ g x w) heq
  have hEval (u : E) :
      fderiv ℝ (fun y => fderiv ℝ f y u) x w =
        (fderiv ℝ (fderiv ℝ f) x w) u := by
    rw [fderiv_clm_apply hR (differentiableAt_const u)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x w =
    fderiv ℝ (fun y => Complex.I • fderiv ℝ f y v) x w at hd
  change fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x w =
    fderiv ℝ (Complex.I • (fun y => fderiv ℝ f y v)) x w at hd
  have hEvalDiff : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    hR.clm_apply (differentiableAt_const v)
  rw [fderiv_const_smul hEvalDiff Complex.I] at hd
  simp only [ContinuousLinearMap.smul_apply] at hd
  rw [hEval v] at hd
  rw [hEval (Complex.I • v)] at hd
  change (fderiv ℝ (fderiv ℝ f) x w) (Complex.I • v) =
    Complex.I • (fderiv ℝ (fderiv ℝ f) x w) v at hd
  exact hd

/-- Symmetry of the real Hessian moves the complex-linearity from its
inner argument to the differentiation direction. -/
theorem real_hessian_commutes_i_outer
    {f : E → F} (hReal : ContDiff ℝ ∞ f)
    (hComplex : Differentiable ℂ f)
    (x v w : E) :
    (fderiv ℝ (fderiv ℝ f) x (Complex.I • w)) v =
      Complex.I • (fderiv ℝ (fderiv ℝ f) x w) v := by
  have hbound : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hs := ((hReal.contDiffAt (x := x)).isSymmSndFDerivAt hbound).eq
  rw [hs (Complex.I • w) v, real_hessian_commutes_i_inner hReal hComplex,
    hs v w]

end
end QuaternionicSymmetry.ComplexSmoothRealHessian
