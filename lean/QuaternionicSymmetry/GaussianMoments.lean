import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! Real Gaussian moments used by the finite curvature-moment calculation.

These statements concern actual Bochner integrals against `gaussianReal`.
They do not assume a formal moment functional agrees with integration.
-/

namespace QuaternionicSymmetry.GaussianMoments

open Polynomial MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- Polynomial factor in repeated derivatives of `exp (v * t² / 2)`. -/
def derivativePolynomial (v : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (derivativePolynomial v n).derivative +
      C v * X * derivativePolynomial v n

theorem hasDerivAt_gaussianExp (v t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (v * x ^ 2 / 2))
      (v * t * Real.exp (v * t ^ 2 / 2)) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2).exp using 1
  simp only [Pi.pow_apply, id_eq]
  ring

theorem iteratedDeriv_gaussianExp (v : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => (derivativePolynomial v n).eval t * Real.exp (v * t ^ 2 / 2) := by
  induction n with
  | zero =>
    funext t
    simp [derivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [((derivativePolynomial v n).hasDerivAt t |>.fun_mul
      (hasDerivAt_gaussianExp v t)).deriv]
    simp only [derivativePolynomial, eval_add, eval_mul, eval_C, eval_X]
    ring

theorem integral_pow_eq_derivativePolynomial (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal 0 v) =
      (derivativePolynomial (v : ℝ) n).eval 0 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) n
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, zero_add] at h
  rw [iteratedDeriv_gaussianExp] at h
  simpa using h.symm


theorem integral_square (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]

theorem integral_fourth (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]
  ring


theorem integral_sixth (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]
  ring

theorem integral_eighth (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 8 ∂gaussianReal 0 v) = 105 * (v : ℝ) ^ 4 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]
  ring

theorem integral_odd_1 (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 1 ∂gaussianReal 0 v) = 0 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]

theorem integral_odd_3 (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) = 0 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]

theorem integral_odd_5 (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 5 ∂gaussianReal 0 v) = 0 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]

theorem integral_odd_7 (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 7 ∂gaussianReal 0 v) = 0 := by
  rw [integral_pow_eq_derivativePolynomial]
  norm_num [derivativePolynomial, Polynomial.derivative_mul]

end
end QuaternionicSymmetry.GaussianMoments
