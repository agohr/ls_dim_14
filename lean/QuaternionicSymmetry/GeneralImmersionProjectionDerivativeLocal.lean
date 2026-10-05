import QuaternionicSymmetry.GeneralImmersionProjectionDerivative

/-! Local-neighborhood version of the derivative of an immersion's
tangent-projection equation, suitable for genuine partial charts. -/

namespace QuaternionicSymmetry.GeneralImmersionProjectionDerivativeLocal

open scoped ContDiff Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem projection_derivative_on_tangent_local
    (f : E → V) (proj : E → V →L[ℝ] V)
    (y u v : E) (hf : ContDiffAt ℝ 2 f y)
    (hproj : DifferentiableAt ℝ proj y)
    (hfix : ∀ᶠ z in 𝓝 y, ∀ w,
      proj z (fderiv ℝ f z w) = fderiv ℝ f z w) :
    (fderiv ℝ proj y u) (fderiv ℝ f y v) +
      proj y (fderiv ℝ (fderiv ℝ f) y u v) =
        fderiv ℝ (fderiv ℝ f) y u v := by
  let dF := fderiv ℝ f
  have hdF : DifferentiableAt ℝ dF y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdFv : DifferentiableAt ℝ (fun z => dF z v) y :=
    hdF.clm_apply (differentiableAt_const _)
  have hfun : (fun z => proj z (dF z v)) =ᶠ[𝓝 y]
      (fun z => dF z v) :=
    hfix.mono (fun z hz => hz v)
  have hd : fderiv ℝ (fun z => proj z (dF z v)) y u =
      fderiv ℝ (fun z => dF z v) y u :=
    congrArg (fun L : E →L[ℝ] V => L u) hfun.fderiv_eq
  rw [fderiv_clm_apply hproj hdFv,
    fderiv_clm_apply hdF (differentiableAt_const v)] at hd
  simpa [dF, add_comm] using hd

end
end QuaternionicSymmetry.GeneralImmersionProjectionDerivativeLocal
