import QuaternionicSymmetry.GaussianMatrixTracePolynomial
import QuaternionicSymmetry.WeightedBlockMatrix
import QuaternionicSymmetry.UniversalGaussianMatrixMoments
import QuaternionicSymmetry.ComplexGaussianExponentialCoefficients

/-! The finite weighted Gaussian matrix moments are quadratic moments of
a repeated block matrix, and therefore have universal trace formulas. -/

namespace QuaternionicSymmetry.GaussianWeightedBlockMoments

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable {α κ S : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  [CommRing S] [Algebra ℂ S]

omit [DecidableEq κ] in
theorem tracePolynomial_eq_quadratic_block (q : α → ℝ) (Y : Matrix κ κ S) :
    GaussianMatrixTracePolynomial.tracePolynomial q Y =
      GaussianQuadraticPolynomial.quadratic (WeightedBlockMatrix.block q Y) := by
  simp only [GaussianMatrixTracePolynomial.tracePolynomial,
    GaussianQuadraticPolynomial.quadratic, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.map_apply, ComplexGaussianMatrix.matrixPolynomial,
    map_sum, map_mul, MvPolynomial.map_C]
  simp only [Fintype.sum_prod_type, WeightedBlockMatrix.block,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.diagonal]
  dsimp only [Matrix.of_apply]
  simp only [ite_mul, zero_mul, apply_ite, map_zero, mul_zero]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset κ))
    (t := (Finset.univ : Finset α))]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul]
  have hq : algebraMap ℂ S (q m : ℂ) = algebraMap ℝ S (q m) := rfl
  rw [hq]
  ring

omit [DecidableEq κ] in
theorem moment_eq_block (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ) :
    GaussianMatrixTracePolynomial.moment q Y k =
      GaussianQuadraticPolynomial.moment (WeightedBlockMatrix.block q Y) k := by
  simp only [GaussianMatrixTracePolynomial.moment, GaussianQuadraticPolynomial.moment,
    tracePolynomial_eq_quadratic_block]

private theorem trace_block (q : α → ℝ) (Y : Matrix κ κ S) :
    Matrix.trace (WeightedBlockMatrix.block q Y) =
      (∑ m, algebraMap ℝ S (q m)) * Matrix.trace Y := by
  simpa only [pow_one] using WeightedBlockMatrix.trace_block_pow q Y 1

theorem normalized_moment_two_eq_eval (q : α → ℝ) (Y : Matrix κ κ S) :
    (1 / 2 : ℝ) • GaussianMatrixTracePolynomial.moment q Y 2 =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S
          (ComplexGaussianExponentialCoefficients.logWeightParameters q i))
        (AhatCoefficientLimits.e₂ (Matrix.trace Y) (Matrix.trace (Y ^ 2))) := by
  rw [moment_eq_block, UniversalGaussianMatrixMoments.moment_two,
    trace_block, WeightedBlockMatrix.trace_block_pow, AhatCoefficientLimits.eval_e₂]
  norm_num [ComplexGaussianExponentialCoefficients.logWeightParameters]
  simp only [Algebra.smul_def, div_eq_mul_inv, map_mul, map_pow, map_sum,
    one_mul]
  ring

theorem normalized_moment_three_eq_eval (q : α → ℝ) (Y : Matrix κ κ S) :
    (1 / 6 : ℝ) • GaussianMatrixTracePolynomial.moment q Y 3 =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S
          (ComplexGaussianExponentialCoefficients.logWeightParameters q i))
        (AhatCoefficientLimits.e₃ (Matrix.trace Y) (Matrix.trace (Y ^ 2))
          (Matrix.trace (Y ^ 3))) := by
  rw [moment_eq_block, UniversalGaussianMatrixMoments.moment_three,
    trace_block, WeightedBlockMatrix.trace_block_pow, WeightedBlockMatrix.trace_block_pow,
    AhatCoefficientLimits.eval_e₃]
  norm_num [ComplexGaussianExponentialCoefficients.logWeightParameters]
  simp only [Algebra.smul_def, div_eq_mul_inv, map_mul, map_pow, map_sum,
    one_mul]
  have h₂ : algebraMap ℝ S (1 / 2) = 3 * algebraMap ℝ S (1 / 6) := by
    calc
      _ = algebraMap ℝ S (3 * (1 / 6)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h₃ : algebraMap ℝ S (1 / 3) = 2 * algebraMap ℝ S (1 / 6) := by
    calc
      _ = algebraMap ℝ S (2 * (1 / 6)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  ring_nf
  rw [h₂, h₃]
  ring

theorem normalized_moment_four_eq_eval (q : α → ℝ) (Y : Matrix κ κ S) :
    (1 / 24 : ℝ) • GaussianMatrixTracePolynomial.moment q Y 4 =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S
          (ComplexGaussianExponentialCoefficients.logWeightParameters q i))
        (AhatCoefficientLimits.e₄ (Matrix.trace Y) (Matrix.trace (Y ^ 2))
          (Matrix.trace (Y ^ 3)) (Matrix.trace (Y ^ 4))) := by
  rw [moment_eq_block, UniversalGaussianMatrixMoments.moment_four,
    trace_block, WeightedBlockMatrix.trace_block_pow, WeightedBlockMatrix.trace_block_pow,
    WeightedBlockMatrix.trace_block_pow, AhatCoefficientLimits.eval_e₄]
  norm_num [ComplexGaussianExponentialCoefficients.logWeightParameters]
  simp only [Algebra.smul_def, div_eq_mul_inv, map_mul, map_pow, map_sum,
    one_mul]
  have h₃ : algebraMap ℝ S (1 / 3) = 8 * algebraMap ℝ S (1 / 24) := by
    calc
      _ = algebraMap ℝ S (8 * (1 / 24)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h₄ : algebraMap ℝ S (1 / 4) = 6 * algebraMap ℝ S (1 / 24) := by
    calc
      _ = algebraMap ℝ S (6 * (1 / 24)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h₂₂ : (algebraMap ℝ S (1 / 2)) ^ 2 = 6 * algebraMap ℝ S (1 / 24) := by
    rw [← map_pow]
    calc
      _ = algebraMap ℝ S (6 * (1 / 24)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h₂₃ : (algebraMap ℝ S (1 / 2)) ^ 3 = 3 * algebraMap ℝ S (1 / 24) := by
    rw [← map_pow]
    calc
      _ = algebraMap ℝ S (3 * (1 / 24)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  ring_nf
  rw [h₃, h₄, h₂₂, h₂₃]
  ring

end
end QuaternionicSymmetry.GaussianWeightedBlockMoments
