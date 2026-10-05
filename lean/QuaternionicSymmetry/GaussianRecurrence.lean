import QuaternionicSymmetry.GaussianMoments
import QuaternionicSymmetry.GaussianMomentPolynomials
import QuaternionicSymmetry.GaussianCombination
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! The two-step moment recurrence for actual centred Gaussian integration. -/

namespace QuaternionicSymmetry.GaussianMoments

open Polynomial MeasureTheory ProbabilityTheory
open scoped NNReal

theorem derivativePolynomial_derivative_succ (v : ℝ) (n : ℕ) :
    (derivativePolynomial v (n + 1)).derivative =
      C (((n + 1 : ℕ) : ℝ) * v) * derivativePolynomial v n := by
  induction n with
  | zero => norm_num [derivativePolynomial, Polynomial.derivative_mul]
  | succ n ih =>
      rw [derivativePolynomial, ih]
      simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
        zero_mul, zero_add, mul_one]
      rw [ih]
      have hrec : derivativePolynomial v (n + 1) =
          (derivativePolynomial v n).derivative + C v * X * derivativePolynomial v n := rfl
      rw [hrec]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_one]
      ring

theorem derivativePolynomial_eval_recurrence (v : ℝ) (n : ℕ) :
    (derivativePolynomial v (n + 2)).eval 0 =
      ((n + 1 : ℕ) : ℝ) * v * (derivativePolynomial v n).eval 0 := by
  rw [derivativePolynomial, derivativePolynomial_derivative_succ]
  simp

/-- The Gaussian moment recurrence, including zero variance. -/
theorem integral_pow_recurrence (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 2) ∂gaussianReal 0 v) =
      ((n + 1 : ℕ) : ℝ) * (v : ℝ) * (∫ x : ℝ, x ^ n ∂gaussianReal 0 v) := by
  rw [integral_pow_eq_derivativePolynomial, integral_pow_eq_derivativePolynomial]
  exact derivativePolynomial_eval_recurrence _ _

theorem integral_odd (v : ℝ≥0) (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂gaussianReal 0 v) = 0 := by
  induction k with
  | zero => exact integral_odd_1 v
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        integral_pow_recurrence, ih, mul_zero]

/-- Every even Gaussian moment, with the convention `0‼ = 1` at order zero. -/
theorem integral_even (v : ℝ≥0) (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) * (v : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one]
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, integral_pow_recurrence, ih, pow_succ]
      push_cast
      ring

/-- The formal moment polynomials agree with actual integration in every order. -/
theorem integral_eq_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal 0 v) =
      GaussianMomentPolynomials.moment n (v : ℝ) := by
  unfold GaussianMomentPolynomials.moment
  split_ifs with hn
  · have h : n = 2 * (n / 2) := by omega
    rw [h]
    simpa using integral_even v (n / 2)
  · have h : n = 2 * (n / 2) + 1 := by omega
    rw [h]
    exact integral_odd v (n / 2)

end QuaternionicSymmetry.GaussianMoments

namespace QuaternionicSymmetry.GaussianCombination

open MeasureTheory ProbabilityTheory

/-- All moments of the finite real Gaussian combination on the explicit product space. -/
theorem product_combination_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (n : ℕ) :
    (∫ ω : ι → ℝ, combination t (fun i ω => ω i) ω ^ n
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      GaussianMomentPolynomials.moment n (variance t : ℝ) := by
  rw [integral_pow_of_hasLaw (product_combination_hasLaw t)]
  exact GaussianMoments.integral_eq_moment _ _

end QuaternionicSymmetry.GaussianCombination
