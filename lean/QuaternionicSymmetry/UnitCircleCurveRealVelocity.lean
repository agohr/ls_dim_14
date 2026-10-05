import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm

/-! A differentiable curve through 1 on the unit circle has purely
imaginary velocity. This is Fermat's theorem for its real part. -/

namespace QuaternionicSymmetry.UnitCircleCurveRealVelocity

open Filter
noncomputable section

theorem real_velocity_zero
    (f : ℝ → ℂ) (hf0 : f 0 = 1)
    (hunit : ∀ t, ‖f t‖ = 1)
    (hf : DifferentiableAt ℝ f 0) :
    (((fderiv ℝ f 0) (1 : ℝ)).re) = 0 := by
  let g : ℝ → ℝ := fun t => (f t).re
  have hmax : IsLocalMax g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    dsimp [g]
    simpa [hf0] using (Complex.re_le_norm (f t)).trans_eq (hunit t)
  have hfg : HasFDerivAt g (Complex.reCLM.comp (fderiv ℝ f 0)) 0 := by
    simpa [g, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp 0 hf.hasFDerivAt
  have hzero := hmax.hasDerivAt_eq_zero hfg.hasDerivAt
  have h := congrArg (fun z : ℝ => z) hzero
  simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    hfg.hasDerivAt.deriv] using h

end
end QuaternionicSymmetry.UnitCircleCurveRealVelocity
