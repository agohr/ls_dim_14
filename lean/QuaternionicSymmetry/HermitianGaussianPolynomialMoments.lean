import QuaternionicSymmetry.GaussianComplexIntegration
import QuaternionicSymmetry.GaussianQuadraticPolynomial
import QuaternionicSymmetry.HermitianGaussianMoments

/-! Bridge between coefficientwise Gaussian quadratic polynomials and actual
Hermitian complex Gaussian quadratic-form integrals. -/

namespace QuaternionicSymmetry.HermitianGaussianPolynomialMoments

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
private theorem measurable_gaussianVector :
    Measurable (ComplexMatrixRealification.gaussianVector : (κ × Fin 2 → ℝ) → κ → ℂ) := by
  rw [measurable_pi_iff]
  intro i
  unfold ComplexMatrixRealification.gaussianVector ComplexGaussianVariable.standardComplex
  change Measurable (fun x : κ × Fin 2 → ℝ =>
    (⟨x (i, 0), x (i, 1)⟩ : ℂ) / (Real.sqrt 2 : ℂ))
  have hp : Measurable (fun x : κ × Fin 2 → ℝ => (x (i, 0), x (i, 1))) :=
    (measurable_pi_apply (i, 0)).prodMk (measurable_pi_apply (i, 1))
  have hc : Measurable (fun x : κ × Fin 2 → ℝ =>
      Complex.measurableEquivRealProd.symm (x (i, 0), x (i, 1))) :=
    Complex.measurableEquivRealProd.symm.measurable.comp hp
  exact hc.div measurable_const

/-- The coefficientwise quadratic-polynomial moment is the actual Hermitian
complex Gaussian integral. -/
theorem moment_eq_integral_quad (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (k : ℕ) :
    GaussianQuadraticPolynomial.moment Y k =
      ((∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ k
        ∂ComplexGaussianUnitaryInvariant.standardMeasure : ℝ) : ℂ) := by
  calc
    GaussianQuadraticPolynomial.moment Y k =
        ∫ ω : κ × Fin 2 → ℝ,
          GaussianComplexIntegration.evaluate (GaussianQuadraticPolynomial.quadratic Y ^ k) ω
          ∂GaussianAlgebra.standardMeasure :=
      (GaussianComplexIntegration.integral_evaluate
        (GaussianQuadraticPolynomial.quadratic Y ^ k)).symm
    _ = ∫ ω : κ × Fin 2 → ℝ,
        (((HermitianQuadraticForm.quad Y
          (ComplexMatrixRealification.gaussianVector ω)) ^ k : ℝ) : ℂ)
          ∂GaussianAlgebra.standardMeasure := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [GaussianComplexIntegration.evaluate, MvPolynomial.eval_pow,
        GaussianQuadraticPolynomial.eval_quadratic_complex,
        GaussianComplexIntegration.dotProduct_eq_ofReal_quad Y hY]
      norm_cast
    _ = ((∫ ω : κ × Fin 2 → ℝ,
        (HermitianQuadraticForm.quad Y
          (ComplexMatrixRealification.gaussianVector ω)) ^ k
          ∂GaussianAlgebra.standardMeasure : ℝ) : ℂ) := by
      exact integral_ofReal
    _ = ((∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ k
        ∂ComplexGaussianUnitaryInvariant.standardMeasure : ℝ) : ℂ) := by
      exact congrArg Complex.ofReal
        (integral_map measurable_gaussianVector.aemeasurable
          (HermitianGaussianMoments.quad_pow_integrable Y hY k).aestronglyMeasurable).symm

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

theorem moment_two_complex (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    GaussianQuadraticPolynomial.moment Y 2 =
      Matrix.trace Y ^ 2 + Matrix.trace (Y ^ 2) := by
  rw [moment_eq_integral_quad Y hY, HermitianGaussianMoments.integral_quad_sq Y hY]
  simp only [Complex.ofReal_add, Complex.ofReal_pow,
    ofReal_re_trace Y hY, ofReal_re_trace (Y ^ 2) (hY.pow 2)]

theorem moment_three_complex (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    GaussianQuadraticPolynomial.moment Y 3 =
      Matrix.trace Y ^ 3 + 3 * Matrix.trace Y * Matrix.trace (Y ^ 2) +
        2 * Matrix.trace (Y ^ 3) := by
  rw [moment_eq_integral_quad Y hY, HermitianGaussianMoments.integral_quad_cube Y hY]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, ofReal_re_trace Y hY,
    ofReal_re_trace (Y ^ 2) (hY.pow 2), ofReal_re_trace (Y ^ 3) (hY.pow 3)]

theorem moment_four_complex (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    GaussianQuadraticPolynomial.moment Y 4 =
      Matrix.trace Y ^ 4 + 6 * Matrix.trace Y ^ 2 * Matrix.trace (Y ^ 2) +
        3 * Matrix.trace (Y ^ 2) ^ 2 + 8 * Matrix.trace Y * Matrix.trace (Y ^ 3) +
          6 * Matrix.trace (Y ^ 4) := by
  rw [moment_eq_integral_quad Y hY, HermitianGaussianMoments.integral_quad_fourth Y hY]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, ofReal_re_trace Y hY,
    ofReal_re_trace (Y ^ 2) (hY.pow 2), ofReal_re_trace (Y ^ 3) (hY.pow 3),
    ofReal_re_trace (Y ^ 4) (hY.pow 4)]

end
end QuaternionicSymmetry.HermitianGaussianPolynomialMoments
