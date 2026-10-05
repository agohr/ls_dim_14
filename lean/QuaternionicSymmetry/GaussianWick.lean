import QuaternionicSymmetry.GaussianUniversalWick
import QuaternionicSymmetry.GaussianFunctionalPolynomial
import QuaternionicSymmetry.GaussianFunctional

/-! Wick's formula as an actual scalar integral, in every order.

The coefficients belong to an arbitrary commutative real algebra. A real-linear
functional supplies the scalar integrand; no topology on the algebra is needed.
-/

namespace QuaternionicSymmetry.GaussianWick

open MeasureTheory
open GaussianPolynomialExpectation
open scoped BigOperators

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

omit [DecidableEq ι] in
theorem combination_power_integrable (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (n : ℕ) :
    Integrable (fun ω : ι → ℝ => L (GaussianFunctional.combination θ ω ^ n)) standardMeasure := by
  simpa only [MvPolynomial.eval_pow, eval_linearPolynomial, GaussianFunctional.combination] using
    GaussianFunctionalPolynomial.polynomial_integrable L (linearPolynomial θ ^ n)

theorem integral_combination_power (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (n : ℕ) :
    (∫ ω : ι → ℝ, L (GaussianFunctional.combination θ ω ^ n) ∂standardMeasure) =
      L (GaussianMomentPolynomials.moment n (∑ i, θ i ^ 2)) := by
  have h := GaussianFunctionalPolynomial.integral_polynomial L (linearPolynomial θ ^ n)
  rw [GaussianUniversalWick.moment] at h
  simpa only [MvPolynomial.eval_pow, eval_linearPolynomial, GaussianFunctional.combination] using h

theorem integral_combination_even (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (k : ℕ) :
    (∫ ω : ι → ℝ, L (GaussianFunctional.combination θ ω ^ (2 * k)) ∂standardMeasure) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) * L ((∑ i, θ i ^ 2) ^ k) := by
  rw [integral_combination_power]
  simp only [GaussianMomentPolynomials.moment, Nat.mul_mod_right, ↓reduceIte,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [show (Nat.doubleFactorial (2 * k - 1) : S) * (∑ i, θ i ^ 2) ^ k =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) • (∑ i, θ i ^ 2) ^ k by
    rw [Algebra.smul_def, map_natCast]]
  exact L.map_smul _ _

/-- Averaging converts the sign for every linear combination into the sign for
the power of the sum of squares, including all mixed terms. -/
theorem sum_squares_power_nonneg (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (k : ℕ)
    (h : ∀ t : ι → ℝ, 0 ≤ L (GaussianFunctional.combination θ t ^ (2 * k))) :
    0 ≤ L ((∑ i, θ i ^ 2) ^ k) := by
  have hi : 0 ≤ ∫ t : ι → ℝ, L (GaussianFunctional.combination θ t ^ (2 * k))
      ∂standardMeasure := integral_nonneg h
  rw [integral_combination_even] at hi
  have hc : (0 : ℝ) < (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * k - 1)
  exact (mul_nonneg_iff_of_pos_left hc).mp hi

end
end QuaternionicSymmetry.GaussianWick
