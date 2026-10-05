import QuaternionicSymmetry.UnitaryGaussianAveraging

/-! Moments of weighted squared entries in a Haar unitary column, obtained
from actual Gaussian moments and the radial averaging identity. -/

namespace QuaternionicSymmetry.UnitaryColumnMoments

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem weighted_power_homogeneous (y : κ → ℝ) (k : ℕ)
    (r : ℝ) (hr : 0 ≤ r) (z : κ → ℂ) :
    (∑ i, y i * ‖(r • z) i‖ ^ 2) ^ k =
      r ^ (2 * k) * (∑ i, y i * ‖z i‖ ^ 2) ^ k := by
  have he : (∑ i, y i * ‖(r • z) i‖ ^ 2) =
      r ^ 2 * ∑ i, y i * ‖z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hr]
    ring
  rw [he, mul_pow, ← pow_mul]

theorem radial_moment_mul_weighted_power (y : κ → ℝ) (k : ℕ) (j : κ) :
    ((Fintype.card κ).ascFactorial k : ℝ) *
      (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * ‖(U : Matrix κ κ ℂ) i j‖ ^ 2) ^ k
        ∂UnitaryHaarMeasure.probability) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial y ^ k) := by
  have h := UnitaryGaussianAveraging.radial_moment_mul_average
    (fun z : κ → ℂ => (∑ i, y i * ‖z i‖ ^ 2) ^ k) k (by fun_prop)
    (ComplexGaussianLawMoments.linear_pow_integrable y k)
    (weighted_power_homogeneous y k) j
  simpa only [Matrix.mulVec_single_one, ComplexGaussianLawMoments.integral_linear_pow] using h

theorem integral_weighted_power (y : κ → ℝ) (k : ℕ) (j : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * ‖(U : Matrix κ κ ℂ) i j‖ ^ 2) ^ k
        ∂UnitaryHaarMeasure.probability) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial y ^ k) /
          ((Fintype.card κ).ascFactorial k : ℝ) := by
  have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨j⟩
  have hne : ((Fintype.card κ).ascFactorial k : ℝ) ≠ 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hn]
    exact_mod_cast (Nat.ascFactorial_pos n k).ne'
  apply (eq_div_iff hne).mpr
  simpa only [mul_comm] using radial_moment_mul_weighted_power y k j

theorem integral_row_weighted_power (y : κ → ℝ) (k : ℕ) (j : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * ‖(U : Matrix κ κ ℂ) j i‖ ^ 2) ^ k
        ∂UnitaryHaarMeasure.probability) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial y ^ k) /
          ((Fintype.card κ).ascFactorial k : ℝ) := by
  have h := UnitaryHaarMeasure.integral_inv (fun U : Matrix.unitaryGroup κ ℂ =>
    (∑ i, y i * ‖(U : Matrix κ κ ℂ) j i‖ ^ 2) ^ k)
  simp only [Matrix.UnitaryGroup.inv_apply, Matrix.star_apply, norm_star] at h
  rw [← h]
  exact integral_weighted_power y k j

end
end QuaternionicSymmetry.UnitaryColumnMoments
