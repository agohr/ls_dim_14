import QuaternionicSymmetry.ComplexGaussianFourthMoment

/-! Low factorial moments after separating scalar weights from algebra-valued weights. -/

namespace QuaternionicSymmetry.ComplexGaussianWeightedMoments

open scoped BigOperators
open MvPolynomial ComplexGaussianPolynomial ComplexGaussianRadialMoments
open QuaternionicSymmetry.ComplexGaussianLinearMoments

noncomputable section

variable {α κ S : Type*} [Fintype α] [Fintype κ] [CommRing S] [Algebra ℝ S]

/-- Product-indexed weights with a real scalar factor and an algebra-valued factor. -/
def weights (q : α → ℝ) (y : κ → S) : α × κ → S :=
  fun p => q p.1 • y p.2

/-- Every power sum of product-indexed weighted variables factors. -/
theorem sum_weights_pow (q : α → ℝ) (y : κ → S) (j : ℕ) :
    (∑ p : α × κ, (weights q y p) ^ j) =
      (∑ m, q m ^ j) • ∑ i, y i ^ j := by
  rw [Fintype.sum_prod_type]
  simp only [weights, smul_pow]
  calc
    _ = ∑ m, q m ^ j • ∑ i, y i ^ j := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.smul_sum]
    _ = _ := (Finset.sum_smul).symm

private theorem sum_weights (q : α → ℝ) (y : κ → S) :
    (∑ p : α × κ, weights q y p) = (∑ m, q m) • ∑ i, y i := by
  simpa only [pow_one] using sum_weights_pow q y 1

private theorem map_q_power_sum (q : α → ℝ) (j : ℕ) :
    algebraMap ℝ S (∑ m, q m ^ j) = ∑ m, algebraMap ℝ S (q m) ^ j := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_pow]

/-- The normalized second moment of product-indexed weighted variables. -/
theorem normalized_moment_two (q : α → ℝ) (y : κ → S) [DecidableEq α] [DecidableEq κ] :
    (1 / 2 : ℝ) • expectation (linearPolynomial (weights q y) ^ 2) =
      ((∑ m, q m) ^ 2 / 2) • (∑ i, y i) ^ 2 +
        ((∑ m, q m ^ 2) / 2) • ∑ i, y i ^ 2 := by
  rw [expectation_linear_sq, sum_weights, sum_weights_pow q y 2]
  have hq1 : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    simpa only [pow_one] using map_q_power_sum (S := S) q 1
  have hq2 := map_q_power_sum (S := S) q 2
  rw [show (∑ m, q m) ^ 2 / 2 = (1 / 2 : ℝ) * (∑ m, q m) ^ 2 by ring,
    show (∑ m, q m ^ 2) / 2 = (1 / 2 : ℝ) * (∑ m, q m ^ 2) by ring]
  simp only [Algebra.smul_def, map_mul, map_pow, hq1, hq2]
  ring

/-- The normalized third moment of product-indexed weighted variables. -/
theorem normalized_moment_three (q : α → ℝ) (y : κ → S) [DecidableEq α] [DecidableEq κ] :
    (1 / 6 : ℝ) • expectation (linearPolynomial (weights q y) ^ 3) =
      ((∑ m, q m) ^ 3 / 6) • (∑ i, y i) ^ 3 +
        ((∑ m, q m) * (∑ m, q m ^ 2) / 2) •
          ((∑ i, y i) * (∑ i, y i ^ 2)) +
        ((∑ m, q m ^ 3) / 3) • ∑ i, y i ^ 3 := by
  rw [expectation_linear_cube, sum_weights, sum_weights_pow q y 2,
    sum_weights_pow q y 3]
  have hq1 : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    simpa only [pow_one] using map_q_power_sum (S := S) q 1
  have hq2 := map_q_power_sum (S := S) q 2
  have hq3 := map_q_power_sum (S := S) q 3
  rw [show (∑ m, q m) ^ 3 / 6 = (1 / 6 : ℝ) * (∑ m, q m) ^ 3 by ring,
    show (∑ m, q m) * (∑ m, q m ^ 2) / 2 =
      (1 / 6 : ℝ) * 3 * (∑ m, q m) * (∑ m, q m ^ 2) by ring,
    show (∑ m, q m ^ 3) / 3 = (1 / 6 : ℝ) * 2 * (∑ m, q m ^ 3) by ring]
  simp only [Algebra.smul_def, map_mul, map_pow, hq1, hq2, hq3]
  simp only [map_ofNat]
  ring

/-- The normalized fourth moment of product-indexed weighted variables. -/
theorem normalized_moment_four (q : α → ℝ) (y : κ → S) [DecidableEq α] [DecidableEq κ] :
    (1 / 24 : ℝ) • expectation (linearPolynomial (weights q y) ^ 4) =
      ((∑ m, q m) ^ 4 / 24) • (∑ i, y i) ^ 4 +
        ((∑ m, q m) ^ 2 * (∑ m, q m ^ 2) / 4) •
          ((∑ i, y i) ^ 2 * (∑ i, y i ^ 2)) +
        ((∑ m, q m ^ 2) ^ 2 / 8) • (∑ i, y i ^ 2) ^ 2 +
        ((∑ m, q m) * (∑ m, q m ^ 3) / 3) •
          ((∑ i, y i) * (∑ i, y i ^ 3)) +
        ((∑ m, q m ^ 4) / 4) • ∑ i, y i ^ 4 := by
  rw [QuaternionicSymmetry.ComplexGaussianFourthMoment.expectation_linear_fourth,
    sum_weights, sum_weights_pow q y 2, sum_weights_pow q y 3,
    sum_weights_pow q y 4]
  have hq1 : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    simpa only [pow_one] using map_q_power_sum (S := S) q 1
  have hq2 := map_q_power_sum (S := S) q 2
  have hq3 := map_q_power_sum (S := S) q 3
  have hq4 := map_q_power_sum (S := S) q 4
  rw [show (∑ m, q m) ^ 4 / 24 = (1 / 24 : ℝ) * (∑ m, q m) ^ 4 by ring,
    show (∑ m, q m) ^ 2 * (∑ m, q m ^ 2) / 4 =
      (1 / 24 : ℝ) * 6 * (∑ m, q m) ^ 2 * (∑ m, q m ^ 2) by ring,
    show (∑ m, q m ^ 2) ^ 2 / 8 = (1 / 24 : ℝ) * 3 * (∑ m, q m ^ 2) ^ 2 by ring,
    show (∑ m, q m) * (∑ m, q m ^ 3) / 3 =
      (1 / 24 : ℝ) * 8 * (∑ m, q m) * (∑ m, q m ^ 3) by ring,
    show (∑ m, q m ^ 4) / 4 = (1 / 24 : ℝ) * 6 * (∑ m, q m ^ 4) by ring]
  simp only [Algebra.smul_def, map_mul, map_pow, hq1, hq2, hq3, hq4]
  simp only [map_ofNat]
  ring

end
end QuaternionicSymmetry.ComplexGaussianWeightedMoments
