import QuaternionicSymmetry.GeneralImmersionChartMetricJet

/-! Differentiating the actual tangent-projection equation yields the
normal Hessian as the derivative of the ambient projection field. -/

namespace QuaternionicSymmetry.GeneralImmersionProjectionDerivative

open scoped ContDiff Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem projection_derivative_on_tangent
    (f : E → V) (proj : E → V →L[ℝ] V)
    (y u v : E) (hf : ContDiffAt ℝ 2 f y)
    (hproj : DifferentiableAt ℝ proj y)
    (hfix : ∀ z w, proj z (fderiv ℝ f z w) = fderiv ℝ f z w) :
    (fderiv ℝ proj y u) (fderiv ℝ f y v) +
      proj y (fderiv ℝ (fderiv ℝ f) y u v) =
        fderiv ℝ (fderiv ℝ f) y u v := by
  let dF := fderiv ℝ f
  have hdF : DifferentiableAt ℝ dF y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdFv : DifferentiableAt ℝ (fun z => dF z v) y :=
    hdF.clm_apply (differentiableAt_const _)
  have hfun : (fun z => proj z (dF z v)) = fun z => dF z v :=
    funext (fun z => hfix z v)
  have hd : fderiv ℝ (fun z => proj z (dF z v)) y u =
      fderiv ℝ (fun z => dF z v) y u :=
    congrArg (fun g : E → V => fderiv ℝ g y u) hfun
  rw [fderiv_clm_apply hproj hdFv,
    fderiv_clm_apply hdF (differentiableAt_const v)] at hd
  simpa [dF, add_comm] using hd

end
end QuaternionicSymmetry.GeneralImmersionProjectionDerivative
