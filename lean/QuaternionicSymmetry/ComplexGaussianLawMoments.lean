import QuaternionicSymmetry.GaussianProductCurry
import QuaternionicSymmetry.ComplexGaussianPolynomial
import QuaternionicSymmetry.ComplexGaussianLinearMoments
import QuaternionicSymmetry.ComplexGaussianFourthMoment
import Mathlib.Topology.Algebra.MvPolynomial

/-! Squared-norm polynomial moments of the actual unitary-invariant complex
Gaussian vector law. -/

namespace QuaternionicSymmetry.ComplexGaussianLawMoments

open MeasureTheory
open ComplexGaussianUnitaryInvariant
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ]

theorem polynomial_integrable (p : MvPolynomial κ ℝ) :
    Integrable (fun z : κ → ℂ => p.eval (fun i => ‖z i‖ ^ 2)) standardMeasure := by
  rw [← GaussianProductCurry.vector_hasLaw.map_eq]
  apply (integrable_map_measure ((MvPolynomial.continuous_eval p).comp (by fun_prop)).aestronglyMeasurable
    GaussianProductCurry.vector_hasLaw.aemeasurable).mpr
  exact ComplexGaussianPolynomial.polynomial_integrable p

theorem integral_polynomial (p : MvPolynomial κ ℝ) :
    (∫ z : κ → ℂ, p.eval (fun i => ‖z i‖ ^ 2) ∂standardMeasure) =
      ComplexGaussianPolynomial.expectation p := by
  have h := GaussianProductCurry.vector_hasLaw.integral_comp
    (f := fun z : κ → ℂ => p.eval (fun i => ‖z i‖ ^ 2))
    ((MvPolynomial.continuous_eval p).comp (by fun_prop)).aestronglyMeasurable
  rw [← h]
  exact ComplexGaussianPolynomial.integral_polynomial p

theorem linear_pow_integrable (y : κ → ℝ) (k : ℕ) :
    Integrable (fun z : κ → ℂ => (∑ i, y i * ‖z i‖ ^ 2) ^ k) standardMeasure := by
  simpa [ComplexGaussianLinearMoments.linearPolynomial] using
    polynomial_integrable (ComplexGaussianLinearMoments.linearPolynomial y ^ k)

theorem integral_linear_pow (y : κ → ℝ) (k : ℕ) :
    (∫ z : κ → ℂ, (∑ i, y i * ‖z i‖ ^ 2) ^ k ∂standardMeasure) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial y ^ k) := by
  simpa [ComplexGaussianLinearMoments.linearPolynomial] using
    integral_polynomial (ComplexGaussianLinearMoments.linearPolynomial y ^ k)

theorem radial_pow_integrable (k : ℕ) :
    Integrable (fun z : κ → ℂ => (∑ i, ‖z i‖ ^ 2) ^ k) standardMeasure := by
  simpa only [map_pow, ComplexGaussianRadialMoments.eval_linearRadial] using
    polynomial_integrable ((ComplexGaussianRadialMoments.linearRadial : MvPolynomial κ ℝ) ^ k)

theorem integral_radial_pow (k : ℕ) :
    (∫ z : κ → ℂ, (∑ i, ‖z i‖ ^ 2) ^ k ∂standardMeasure) =
      ((Fintype.card κ).ascFactorial k : ℝ) := by
  classical
  simpa only [map_pow, ComplexGaussianRadialMoments.eval_linearRadial,
    ComplexGaussianRadialMoments.expectation_linearRadial] using
    integral_polynomial ((ComplexGaussianRadialMoments.linearRadial : MvPolynomial κ ℝ) ^ k)

end
end QuaternionicSymmetry.ComplexGaussianLawMoments
