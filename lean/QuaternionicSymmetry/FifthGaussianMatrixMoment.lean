import QuaternionicSymmetry.ComplexGaussianFifthMoment
import QuaternionicSymmetry.HermitianGaussianPolynomialMoments

/-! The fifth complex Gaussian quadratic moment, first for an actual Hermitian
matrix integral and then universally over commutative complex algebras. -/

namespace QuaternionicSymmetry.FifthGaussianMatrixMoment

open Matrix MvPolynomial
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The fifth moment of the actual Hermitian complex Gaussian quadratic form. -/
theorem integral_quad_fifth (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ 5
      ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
      (Matrix.trace Y).re ^ 5 +
        10 * (Matrix.trace Y).re ^ 3 * (Matrix.trace (Y ^ 2)).re +
        15 * (Matrix.trace Y).re * (Matrix.trace (Y ^ 2)).re ^ 2 +
        20 * (Matrix.trace Y).re ^ 2 * (Matrix.trace (Y ^ 3)).re +
        20 * (Matrix.trace (Y ^ 2)).re * (Matrix.trace (Y ^ 3)).re +
        30 * (Matrix.trace Y).re * (Matrix.trace (Y ^ 4)).re +
        24 * (Matrix.trace (Y ^ 5)).re := by
  rw [HermitianGaussianMoments.integral_quad_pow Y hY 5,
    ComplexGaussianFifthMoment.expectation_linear_fifth]
  have ht1 : (Matrix.trace Y).re = ∑ i, hY.eigenvalues i := by
    simpa only [pow_one] using
      HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  have ht2 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2
  have ht3 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 3
  have ht4 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 4
  have ht5 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 5
  rw [← ht1, ← ht2, ← ht3, ← ht4, ← ht5]

omit [DecidableEq κ] in
private theorem ofReal_re_trace (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    ((Matrix.trace Y).re : ℂ) = Matrix.trace Y := by
  have h : star (Matrix.trace Y) = Matrix.trace Y := by
    rw [← Matrix.trace_conjTranspose, hY.eq]
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The fifth polynomial moment of a Hermitian matrix is the same actual
Gaussian integral, viewed in complex coefficients. -/
theorem moment_five_complex (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    GaussianQuadraticPolynomial.moment Y 5 =
      Matrix.trace Y ^ 5 +
        10 * Matrix.trace Y ^ 3 * Matrix.trace (Y ^ 2) +
        15 * Matrix.trace Y * Matrix.trace (Y ^ 2) ^ 2 +
        20 * Matrix.trace Y ^ 2 * Matrix.trace (Y ^ 3) +
        20 * Matrix.trace (Y ^ 2) * Matrix.trace (Y ^ 3) +
        30 * Matrix.trace Y * Matrix.trace (Y ^ 4) +
        24 * Matrix.trace (Y ^ 5) := by
  rw [HermitianGaussianPolynomialMoments.moment_eq_integral_quad Y hY,
    integral_quad_fifth Y hY]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, ofReal_re_trace Y hY,
    ofReal_re_trace (Y ^ 2) (hY.pow 2),
    ofReal_re_trace (Y ^ 3) (hY.pow 3),
    ofReal_re_trace (Y ^ 4) (hY.pow 4),
    ofReal_re_trace (Y ^ 5) (hY.pow 5)]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

private theorem eval_universal_trace_one (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ))) =
        Matrix.trace Y := by
  simpa only [pow_one] using GaussianQuadraticPolynomial.eval_universal_trace_pow Y 1

/-- The fifth matrix-moment identity extends to every commutative complex
algebra, including the even-form algebra with nilpotent coefficients. -/
theorem moment_five (Y : Matrix κ κ S) :
    GaussianQuadraticPolynomial.moment Y 5 =
      Matrix.trace Y ^ 5 +
        10 * Matrix.trace Y ^ 3 * Matrix.trace (Y ^ 2) +
        15 * Matrix.trace Y * Matrix.trace (Y ^ 2) ^ 2 +
        20 * Matrix.trace Y ^ 2 * Matrix.trace (Y ^ 3) +
        20 * Matrix.trace (Y ^ 2) * Matrix.trace (Y ^ 3) +
        30 * Matrix.trace Y * Matrix.trace (Y ^ 4) +
        24 * Matrix.trace (Y ^ 5) := by
  let U : Matrix κ κ (MvPolynomial (κ × κ) ℂ) :=
    GaussianQuadraticPolynomial.universalMatrix
  let p : MvPolynomial (κ × κ) ℂ :=
    Matrix.trace U ^ 5 +
      10 * Matrix.trace U ^ 3 * Matrix.trace (U ^ 2) +
      15 * Matrix.trace U * Matrix.trace (U ^ 2) ^ 2 +
      20 * Matrix.trace U ^ 2 * Matrix.trace (U ^ 3) +
      20 * Matrix.trace (U ^ 2) * Matrix.trace (U ^ 3) +
      30 * Matrix.trace U * Matrix.trace (U ^ 4) +
      24 * Matrix.trace (U ^ 5)
  have h := GaussianQuadraticPolynomial.extend_moment_identity 5 p
    (fun A hA => by
      simpa only [p, U, map_add, map_mul, map_pow, map_ofNat,
        GaussianQuadraticPolynomial.eval_universal_trace_pow,
        eval_universal_trace_one] using
        moment_five_complex A hA) Y
  rw [h]
  simp only [p, U, map_add, map_mul, map_pow, map_ofNat,
    GaussianQuadraticPolynomial.eval_universal_trace_pow,
    eval_universal_trace_one]

end
end QuaternionicSymmetry.FifthGaussianMatrixMoment
