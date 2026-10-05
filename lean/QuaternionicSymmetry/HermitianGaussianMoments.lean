import QuaternionicSymmetry.HermitianQuadraticForm
import QuaternionicSymmetry.ComplexGaussianLawMoments
import QuaternionicSymmetry.ComplexGaussianUnitaryInvariant

/-! Actual complex-Gaussian moments of finite Hermitian quadratic forms. -/

namespace QuaternionicSymmetry.HermitianGaussianMoments

open MeasureTheory
open scoped BigOperators ComplexOrder
open Matrix

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
private theorem measurable_mulVec (U : Matrix κ κ ℂ) :
    Measurable (Matrix.mulVec U : (κ → ℂ) → κ → ℂ) := by
  rw [measurable_pi_iff]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private theorem eigenvectorUnitary_isUnitary (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix κ κ ℂ) *
      (star (hY.eigenvectorUnitary : Matrix κ κ ℂ)).conjTranspose = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Unitary.coe_star_mul_self hY.eigenvectorUnitary

/-- Powers of a Hermitian quadratic form are integrable for the actual unitary-invariant
complex Gaussian vector law. -/
theorem quad_pow_integrable (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (k : ℕ) :
    Integrable (fun z : κ → ℂ => (HermitianQuadraticForm.quad Y z) ^ k)
      ComplexGaussianUnitaryInvariant.standardMeasure := by
  let U : Matrix κ κ ℂ := star (hY.eigenvectorUnitary : Matrix κ κ ℂ)
  let g : (κ → ℂ) → ℝ := fun z => (∑ i, hY.eigenvalues i * ‖z i‖ ^ 2) ^ k
  have hU : U * U.conjTranspose = 1 := eigenvectorUnitary_isUnitary Y hY
  have hg : Integrable g ComplexGaussianUnitaryInvariant.standardMeasure := by
    exact ComplexGaussianLawMoments.linear_pow_integrable hY.eigenvalues k
  have hgmap : Integrable g
      (Measure.map (Matrix.mulVec U) ComplexGaussianUnitaryInvariant.standardMeasure) := by
    rw [ComplexGaussianUnitaryInvariant.map_mulVec_standardMeasure U hU]
    exact hg
  have hcomp := hgmap.comp_aemeasurable (measurable_mulVec U).aemeasurable
  convert hcomp using 1
  funext z
  rw [HermitianQuadraticForm.quad_spectral]
  rfl

/-- The actual integral of a Hermitian quadratic-form power is its factorial complex-radial
polynomial expectation in spectral coordinates. -/
theorem integral_quad_pow (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (k : ℕ) :
    (∫ z : κ → ℂ, (HermitianQuadraticForm.quad Y z) ^ k
      ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial hY.eigenvalues ^ k) := by
  let U : Matrix κ κ ℂ := star (hY.eigenvectorUnitary : Matrix κ κ ℂ)
  let g : (κ → ℂ) → ℝ := fun z => (∑ i, hY.eigenvalues i * ‖z i‖ ^ 2) ^ k
  have hU : U * U.conjTranspose = 1 := eigenvectorUnitary_isUnitary Y hY
  have hg : Integrable g ComplexGaussianUnitaryInvariant.standardMeasure := by
    exact ComplexGaussianLawMoments.linear_pow_integrable hY.eigenvalues k
  calc
    (∫ z : κ → ℂ, (HermitianQuadraticForm.quad Y z) ^ k
        ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
        ∫ z : κ → ℂ, g (Matrix.mulVec U z)
          ∂ComplexGaussianUnitaryInvariant.standardMeasure := by
      congr 1
      funext z
      rw [HermitianQuadraticForm.quad_spectral]
    _ = ∫ z : κ → ℂ, g z ∂ComplexGaussianUnitaryInvariant.standardMeasure := by
      exact ComplexGaussianUnitaryInvariant.integral_mulVec_standardMeasure U hU g
        hg.aestronglyMeasurable
    _ = _ := by
      exact ComplexGaussianLawMoments.integral_linear_pow hY.eigenvalues k

/-- The second complex-Gaussian moment of a Hermitian quadratic form. -/
theorem integral_quad_sq (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ 2
      ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
      (Matrix.trace Y).re ^ 2 + (Matrix.trace (Y ^ 2)).re := by
  rw [integral_quad_pow Y hY 2,
    ComplexGaussianLinearMoments.expectation_linear_sq]
  have ht1 : (Matrix.trace Y).re = ∑ i, hY.eigenvalues i := by
    simpa only [pow_one] using
      HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  have ht2 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2
  rw [← ht1, ← ht2]

/-- The third complex-Gaussian moment of a Hermitian quadratic form. -/
theorem integral_quad_cube (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ 3
      ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
      (Matrix.trace Y).re ^ 3 +
        3 * (Matrix.trace Y).re * (Matrix.trace (Y ^ 2)).re +
          2 * (Matrix.trace (Y ^ 3)).re := by
  rw [integral_quad_pow Y hY 3,
    ComplexGaussianLinearMoments.expectation_linear_cube]
  have ht1 : (Matrix.trace Y).re = ∑ i, hY.eigenvalues i := by
    simpa only [pow_one] using
      HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  have ht2 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2
  have ht3 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 3
  rw [← ht1, ← ht2, ← ht3]

/-- The fourth complex-Gaussian moment of a Hermitian quadratic form. -/
theorem integral_quad_fourth (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ z : κ → ℂ, HermitianQuadraticForm.quad Y z ^ 4
      ∂ComplexGaussianUnitaryInvariant.standardMeasure) =
      (Matrix.trace Y).re ^ 4 +
        6 * (Matrix.trace Y).re ^ 2 * (Matrix.trace (Y ^ 2)).re +
          3 * (Matrix.trace (Y ^ 2)).re ^ 2 +
            8 * (Matrix.trace Y).re * (Matrix.trace (Y ^ 3)).re +
              6 * (Matrix.trace (Y ^ 4)).re := by
  rw [integral_quad_pow Y hY 4,
    QuaternionicSymmetry.ComplexGaussianFourthMoment.expectation_linear_fourth]
  have ht1 : (Matrix.trace Y).re = ∑ i, hY.eigenvalues i := by
    simpa only [pow_one] using
      HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  have ht2 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2
  have ht3 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 3
  have ht4 := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 4
  rw [← ht1, ← ht2, ← ht3, ← ht4]

end
end QuaternionicSymmetry.HermitianGaussianMoments
