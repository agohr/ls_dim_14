import QuaternionicSymmetry.GaussianPolynomialIntegration
import QuaternionicSymmetry.GaussianPolynomialExpectation

/-! Universal Gaussian moments by polynomial continuation from actual real integrals. -/

namespace QuaternionicSymmetry.GaussianUniversalWick

open MeasureTheory ProbabilityTheory
open GaussianPolynomialExpectation
open scoped BigOperators

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

private theorem scalar_moment (t : ι → ℝ) (n : ℕ) :
    expectation (linearPolynomial t ^ n) =
      GaussianMomentPolynomials.moment n (∑ i, t i ^ 2) := by
  rw [← GaussianPolynomialIntegration.integral_polynomial]
  have h := GaussianCombination.product_combination_moment t n
  simpa [GaussianPolynomialIntegration.standardMeasure, GaussianAlgebra.standardMeasure,
    GaussianCombination.combination, GaussianCombination.variance,
    linearPolynomial] using h

/-- A polynomial identity in independent coefficient variables, in every order. -/
theorem universal_moment (n : ℕ) :
    expectation (linearPolynomial (fun i : ι => MvPolynomial.X i : ι → MvPolynomial ι ℝ) ^ n) =
      GaussianMomentPolynomials.moment n (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℝ) ^ 2) := by
  apply MvPolynomial.funext
  intro t
  change (MvPolynomial.aeval t) _ = (MvPolynomial.aeval t) _
  rw [expectation_map]
  rw [algHom_moment]
  simp only [map_pow, map_linearPolynomial, MvPolynomial.aeval_X, map_sum]
  exact scalar_moment t n

/-- Wick's moment formula in any commutative real algebra, including nilpotents. -/
theorem moment (θ : ι → S) (n : ℕ) :
    expectation (linearPolynomial θ ^ n) =
      GaussianMomentPolynomials.moment n (∑ i, θ i ^ 2) := by
  have h := congrArg (MvPolynomial.aeval θ) (universal_moment (ι := ι) n)
  rw [expectation_map] at h
  rw [algHom_moment] at h
  simpa only [map_pow, map_linearPolynomial, MvPolynomial.aeval_X, map_sum] using h

theorem even_moment (θ : ι → S) (k : ℕ) :
    expectation (linearPolynomial θ ^ (2 * k)) =
      (Nat.doubleFactorial (2 * k - 1) : S) * (∑ i, θ i ^ 2) ^ k := by
  rw [moment]
  simp [GaussianMomentPolynomials.moment]

end
end QuaternionicSymmetry.GaussianUniversalWick
