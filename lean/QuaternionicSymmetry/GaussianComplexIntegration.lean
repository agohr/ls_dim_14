import QuaternionicSymmetry.GaussianFunctionalPolynomial
import QuaternionicSymmetry.HermitianQuadraticForm

/-! Actual complex Bochner integration of polynomials in finite real Gaussian
coordinates, and the Hermitian reality of the associated quadratic form. -/

namespace QuaternionicSymmetry.GaussianComplexIntegration

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Evaluate a complex-coefficient polynomial at finite real Gaussian coordinates. -/
def evaluate (p : MvPolynomial ι ℂ) (ω : ι → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (ω i : ℂ)) p

omit [Fintype ι] in
private theorem evaluate_eq_algebraMap (p : MvPolynomial ι ℂ) (ω : ι → ℝ) :
    evaluate p ω = MvPolynomial.eval (fun i => algebraMap ℝ ℂ (ω i)) p := by
  rfl

/-- Complex polynomial evaluation on the finite standard Gaussian product is integrable. -/
theorem evaluate_integrable (p : MvPolynomial ι ℂ) :
    Integrable (evaluate p) (GaussianAlgebra.standardMeasure (ι := ι)) := by
  have hre := GaussianFunctionalPolynomial.polynomial_integrable (ι := ι) Complex.reLm p
  have him := GaussianFunctionalPolynomial.polynomial_integrable (ι := ι) Complex.imLm p
  have hsum : Integrable (fun ω : ι → ℝ =>
      (Complex.re (evaluate p ω) : ℂ) + Complex.I * (Complex.im (evaluate p ω) : ℂ))
      (GaussianAlgebra.standardMeasure (ι := ι)) := by
    apply hre.ofReal.add (him.ofReal.const_mul Complex.I)
  apply hsum.congr
  filter_upwards [] with ω
  rw [mul_comm Complex.I, Complex.re_add_im]

/-- The actual complex Gaussian polynomial integral is its coefficientwise expectation. -/
theorem integral_evaluate (p : MvPolynomial ι ℂ) :
    (∫ ω : ι → ℝ, evaluate p ω ∂GaussianAlgebra.standardMeasure) =
      GaussianPolynomialExpectation.expectation p := by
  have hp := evaluate_integrable p
  apply Complex.ext
  · change RCLike.re (∫ ω : ι → ℝ, evaluate p ω ∂GaussianAlgebra.standardMeasure) =
      RCLike.re (GaussianPolynomialExpectation.expectation p)
    rw [← integral_re hp]
    simpa only [evaluate, Complex.reLm_coe] using
      GaussianFunctionalPolynomial.integral_polynomial (ι := ι) Complex.reLm p
  · change RCLike.im (∫ ω : ι → ℝ, evaluate p ω ∂GaussianAlgebra.standardMeasure) =
      RCLike.im (GaussianPolynomialExpectation.expectation p)
    rw [← integral_im hp]
    simpa only [evaluate, Complex.imLm_coe] using
      GaussianFunctionalPolynomial.integral_polynomial (ι := ι) Complex.imLm p

/-- A Hermitian quadratic form has no imaginary part. -/
theorem dotProduct_eq_ofReal_quad {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (v : κ → ℂ) :
    dotProduct (star v) (Y.mulVec v) = (HermitianQuadraticForm.quad Y v : ℂ) := by
  apply Complex.ext
  · simp [HermitianQuadraticForm.quad]
  · change RCLike.im (dotProduct (star v) (Y.mulVec v)) =
      RCLike.im (HermitianQuadraticForm.quad Y v : ℂ)
    rw [Matrix.IsHermitian.im_star_dotProduct_mulVec_self hY v]
    simp [HermitianQuadraticForm.quad]

end
end QuaternionicSymmetry.GaussianComplexIntegration
