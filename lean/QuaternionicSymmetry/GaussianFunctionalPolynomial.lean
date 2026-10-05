import QuaternionicSymmetry.GaussianPolynomialIntegration
import QuaternionicSymmetry.GaussianPolynomialExpectation

/-! Polynomial Gaussian integration after an arbitrary real-linear functional. -/

namespace QuaternionicSymmetry.GaussianFunctionalPolynomial

open MeasureTheory ProbabilityTheory
open GaussianPolynomialExpectation
open scoped BigOperators

noncomputable section

variable {ι S : Type*} [Fintype ι] [CommRing S] [Algebra ℝ S]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

private theorem apply_scalar (L : S →ₗ[ℝ] ℝ) (c : S) (r : ℝ) :
    L (c * algebraMap ℝ S r) = L c * r := by
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm r]

private theorem eval_monomial (L : S →ₗ[ℝ] ℝ) (d : ι →₀ ℕ) (c : S) (ω : ι → ℝ) :
    L (MvPolynomial.eval (fun i => algebraMap ℝ S (ω i)) (MvPolynomial.monomial d c)) =
      MvPolynomial.eval ω (MvPolynomial.monomial d (L c)) := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  simp only [← map_pow, ← map_prod]
  exact apply_scalar L c _

theorem polynomial_integrable (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι S) :
    Integrable (fun ω : ι → ℝ => L (MvPolynomial.eval (fun i => algebraMap ℝ S (ω i)) p))
      standardMeasure := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp_rw [eval_monomial]
      exact GaussianPolynomialIntegration.monomial_integrable d (L c)
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq

theorem integral_polynomial (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι S) :
    (∫ ω : ι → ℝ, L (MvPolynomial.eval (fun i => algebraMap ℝ S (ω i)) p) ∂standardMeasure) =
      L (expectation p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp_rw [eval_monomial]
      rw [GaussianPolynomialIntegration.integral_monomial, expectation_monomial, apply_scalar]
      rfl
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (polynomial_integrable L p) (polynomial_integrable L q), hp, hq]

end
end QuaternionicSymmetry.GaussianFunctionalPolynomial
