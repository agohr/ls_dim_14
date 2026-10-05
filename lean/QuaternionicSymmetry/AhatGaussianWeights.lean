import QuaternionicSymmetry.LogAhat
import Mathlib.NumberTheory.ZetaValues

/-! The Gaussian weights in the positive A-hat series are summable, and their
power sums equal the signed logarithmic Bernoulli coefficients. -/

namespace QuaternionicSymmetry.AhatGaussianWeights

open scoped BigOperators

noncomputable section

/-- The zero index contributes zero; positive indices are the textbook weights. -/
def weight (m : ℕ) : ℝ := 1 / (4 * Real.pi ^ 2 * (m : ℝ) ^ 2)

def positiveLog (j : ℕ) : ℝ := (-1 : ℝ) ^ j * (LogAhat.ell j : ℝ)

@[simp] theorem weight_zero : weight 0 = 0 := by simp [weight]

theorem weight_nonneg (m : ℕ) : 0 ≤ weight m := by unfold weight; positivity

theorem weight_pos {m : ℕ} (hm : m ≠ 0) : 0 < weight m := by
  unfold weight
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  positivity

theorem weight_pow (m j : ℕ) :
    weight m ^ j = (4 * Real.pi ^ 2)⁻¹ ^ j * (1 / (m : ℝ) ^ (2 * j)) := by
  simp only [weight, one_div, mul_inv_rev, mul_pow, inv_pow, pow_mul]
  ring

theorem summable_power {j : ℕ} (hj : 0 < j) : Summable (fun m => weight m ^ j) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * j)).mul_left
    ((4 * Real.pi ^ 2)⁻¹ ^ j)
  simpa only [← weight_pow] using h

theorem summable_weight : Summable weight := by
  simpa only [pow_one] using summable_power (j := 1) (by omega)

theorem hasSum_power {j : ℕ} (hj : 0 < j) :
    HasSum (fun m => weight m ^ j) ((j : ℝ) * positiveLog j) := by
  have h := (hasSum_zeta_nat (Nat.ne_of_gt hj)).mul_left ((4 * Real.pi ^ 2)⁻¹ ^ j)
  simp only [← weight_pow] at h
  have htwo : (2 : ℝ) ^ (2 * j - 1) = 2 ^ (2 * j) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * j)]
  have hp : (4 * Real.pi ^ 2) ^ j = (2 : ℝ) ^ (2 * j) * Real.pi ^ (2 * j) := by
    rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  convert h using 1
  simp only [positiveLog, LogAhat.ell, Rat.cast_div, Rat.cast_neg, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_ofNat]
  rw [inv_pow, hp, htwo, pow_succ]
  field_simp [hj', Real.pi_ne_zero]

theorem tsum_power {j : ℕ} (hj : 0 < j) :
    (∑' m, weight m ^ j) = (j : ℝ) * positiveLog j := (hasSum_power hj).tsum_eq

theorem positiveLog_pos {j : ℕ} (hj : 0 < j) : 0 < positiveLog j := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  apply (mul_pos_iff_of_pos_left hj').mp
  rw [← tsum_power hj]
  exact (summable_power hj).tsum_pos (fun m => pow_nonneg (weight_nonneg m) j) 1
    (pow_pos (weight_pos one_ne_zero) j)

theorem partial_log_tendsto {j : ℕ} (hj : 0 < j) :
    Filter.Tendsto (fun N => (∑ m ∈ Finset.range N, weight m ^ j) / (j : ℝ))
      Filter.atTop (nhds (positiveLog j)) := by
  have h := (hasSum_power hj).tendsto_sum_nat.div_const (j : ℝ)
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  simpa only [mul_div_cancel_left₀ _ hj'] using h

@[simp] theorem positiveLog_one : positiveLog 1 = 1 / 24 := by
  norm_num [positiveLog, LogAhat.ell_one]

@[simp] theorem positiveLog_two : positiveLog 2 = 1 / 2880 := by
  norm_num [positiveLog, LogAhat.ell_two]

@[simp] theorem positiveLog_three : positiveLog 3 = 1 / 181440 := by
  norm_num [positiveLog, LogAhat.ell_three]

@[simp] theorem positiveLog_four : positiveLog 4 = 1 / 9676800 := by
  norm_num [positiveLog, LogAhat.ell_four]

end
end QuaternionicSymmetry.AhatGaussianWeights
