import QuaternionicSymmetry.AhatCoefficientLimits

/-! Closed positive-ray passage for the finite A-hat coefficient
approximations.  The hypotheses remain finite evaluation statements; this
module makes no claim that they arise from a Gaussian or geometric argument. -/

namespace QuaternionicSymmetry.AhatPositiveLimits

open Filter Topology

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S]

theorem contains_e₂_limit
    {v : S} (hv : v ≠ 0) (z₁ z₂ w : S)
    (hp : ∀ N, PositiveRay.Contains v
      (MvPolynomial.eval
        (fun i => algebraMap ℝ S (AhatCoefficientLimits.logParameters N i))
        (AhatCoefficientLimits.e₂ z₁ z₂ * MvPolynomial.C w))) :
    PositiveRay.Contains v
      ((algebraMap ℝ S (1 / 1152) * z₁ ^ 2 +
        algebraMap ℝ S (1 / 2880) * z₂) * w) := by
  have h := AlgebraPolynomialLimits.contains_of_tendsto hv
    (AhatCoefficientLimits.e₂ z₁ z₂ * MvPolynomial.C w)
    AhatCoefficientLimits.logParameters AhatCoefficientLimits.logLimit
    AhatCoefficientLimits.logParameters_tendsto hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    AhatCoefficientLimits.e₂_limit_eval] using h

theorem contains_e₃_limit
    {v : S} (hv : v ≠ 0) (z₁ z₂ z₃ w : S)
    (hp : ∀ N, PositiveRay.Contains v
      (MvPolynomial.eval
        (fun i => algebraMap ℝ S (AhatCoefficientLimits.logParameters N i))
        (AhatCoefficientLimits.e₃ z₁ z₂ z₃ * MvPolynomial.C w))) :
    PositiveRay.Contains v
      ((algebraMap ℝ S (1 / 82944) * z₁ ^ 3 +
        algebraMap ℝ S (1 / 69120) * z₁ * z₂ +
        algebraMap ℝ S (1 / 181440) * z₃) * w) := by
  have h := AlgebraPolynomialLimits.contains_of_tendsto hv
    (AhatCoefficientLimits.e₃ z₁ z₂ z₃ * MvPolynomial.C w)
    AhatCoefficientLimits.logParameters AhatCoefficientLimits.logLimit
    AhatCoefficientLimits.logParameters_tendsto hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    AhatCoefficientLimits.e₃_limit_eval] using h

theorem contains_e₄_limit
    {v : S} (hv : v ≠ 0) (z₁ z₂ z₃ z₄ w : S)
    (hp : ∀ N, PositiveRay.Contains v
      (MvPolynomial.eval
        (fun i => algebraMap ℝ S (AhatCoefficientLimits.logParameters N i))
        (AhatCoefficientLimits.e₄ z₁ z₂ z₃ z₄ * MvPolynomial.C w))) :
    PositiveRay.Contains v
      ((algebraMap ℝ S (1 / 7962624) * z₁ ^ 4 +
        algebraMap ℝ S (1 / 3317760) * z₁ ^ 2 * z₂ +
        algebraMap ℝ S (1 / 16588800) * z₂ ^ 2 +
        algebraMap ℝ S (1 / 4354560) * z₁ * z₃ +
        algebraMap ℝ S (1 / 9676800) * z₄) * w) := by
  have h := AlgebraPolynomialLimits.contains_of_tendsto hv
    (AhatCoefficientLimits.e₄ z₁ z₂ z₃ z₄ * MvPolynomial.C w)
    AhatCoefficientLimits.logParameters AhatCoefficientLimits.logLimit
    AhatCoefficientLimits.logParameters_tendsto hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    AhatCoefficientLimits.e₄_limit_eval] using h

end
end QuaternionicSymmetry.AhatPositiveLimits
