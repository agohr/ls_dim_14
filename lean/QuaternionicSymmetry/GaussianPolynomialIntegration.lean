import QuaternionicSymmetry.GaussianRecurrence
import QuaternionicSymmetry.GaussianAlgebra
import QuaternionicSymmetry.GaussianPolynomialExpectation
import Mathlib.Algebra.MvPolynomial.Eval

namespace QuaternionicSymmetry.GaussianPolynomialIntegration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]
abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

omit [Fintype ι] in
private theorem coordinate_pow_integrable (d : ι →₀ ℕ) (i : ι) :
    Integrable (fun x : ℝ ↦ x ^ d i) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) _

theorem monomial_integrable (d : ι →₀ ℕ) (c : ℝ) :
    Integrable (fun ω : ι → ℝ ↦ (MvPolynomial.monomial d c).eval ω) standardMeasure := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  exact (Integrable.fintype_prod fun i ↦ coordinate_pow_integrable d i).const_mul c

theorem integral_monomial (d : ι →₀ ℕ) (c : ℝ) :
    (∫ ω : ι → ℝ, (MvPolynomial.monomial d c).eval ω ∂standardMeasure) =
      c * ∏ i, GaussianMomentPolynomials.moment (d i) (1 : ℝ) := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  rw [integral_const_mul]
  change c * (∫ ω : ι → ℝ, ∏ i, ω i ^ d i
    ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = _
  congr 1
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun i x ↦ x ^ d i)]
  apply Finset.prod_congr rfl
  intro i _
  exact GaussianMoments.integral_eq_moment _ _

theorem polynomial_integrable (p : MvPolynomial ι ℝ) :
    Integrable (fun ω : ι → ℝ ↦ p.eval ω) standardMeasure := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => exact monomial_integrable d c
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq

theorem integral_polynomial (p : MvPolynomial ι ℝ) :
    (∫ ω : ι → ℝ, p.eval ω ∂standardMeasure) =
      GaussianPolynomialExpectation.expectation p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simpa [GaussianPolynomialExpectation.monomialMoment] using integral_monomial d c
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (polynomial_integrable p) (polynomial_integrable q), hp, hq]
end
end QuaternionicSymmetry.GaussianPolynomialIntegration
