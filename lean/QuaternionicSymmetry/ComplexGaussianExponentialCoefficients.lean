import QuaternionicSymmetry.ComplexGaussianWeightedMoments
import QuaternionicSymmetry.AhatCoefficientLimits

/-! The normalized finite weighted moments are evaluations of the same
exponential coefficient polynomials used for the A-hat limits.  This is an
algebraic identification only; no limiting or Gaussian-measure statement is
made here. -/

namespace QuaternionicSymmetry.ComplexGaussianExponentialCoefficients

open scoped BigOperators
open QuaternionicSymmetry.AhatCoefficientLimits
open QuaternionicSymmetry.ComplexGaussianWeightedMoments
open QuaternionicSymmetry.ComplexGaussianLinearMoments
open MvPolynomial ComplexGaussianPolynomial

noncomputable section

variable {α κ S : Type*} [Fintype α] [Fintype κ]
  [CommRing S] [Algebra ℝ S]

def logWeightParameters (q : α → ℝ) (i : Fin 4) : ℝ :=
  (∑ m, q m ^ (i.val + 1)) / ((i.val : ℝ) + 1)

theorem normalized_moment_two_eq_eval (q : α → ℝ) (y : κ → S)
    [DecidableEq α] [DecidableEq κ] :
    (1 / 2 : ℝ) • expectation (linearPolynomial (weights q y) ^ 2) =
    MvPolynomial.eval
        (fun i => algebraMap ℝ S (logWeightParameters q i))
        (e₂ (∑ i, y i) (∑ i, y i ^ 2)) := by
  rw [normalized_moment_two, eval_e₂]
  have h₀ : logWeightParameters q (0 : Fin 4) = ∑ m, q m := by
    simp [logWeightParameters]
  have h₁ : logWeightParameters q (1 : Fin 4) =
      (1 / 2 : ℝ) * ∑ m, q m ^ 2 := by
    norm_num [logWeightParameters]
    ring
  have hq₁ : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    rw [map_sum]
  have hq₂ : algebraMap ℝ S (∑ m, q m ^ 2) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 2 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  rw [h₀, h₁]
  simp only [Algebra.smul_def]
  rw [show (∑ m, q m) ^ 2 / 2 = (∑ m, q m) ^ 2 * (1 / 2 : ℝ) by ring,
    show (∑ m, q m ^ 2) / 2 = (∑ m, q m ^ 2) * (1 / 2 : ℝ) by ring]
  have hmap_mul (a b : ℝ) : algebraMap ℝ S (a * b) =
      algebraMap ℝ S a * algebraMap ℝ S b := by rw [map_mul]
  have hmap_pow (a : ℝ) (n : ℕ) : algebraMap ℝ S (a ^ n) =
      (algebraMap ℝ S a) ^ n := by rw [map_pow]
  have hmap_one : algebraMap ℝ S (1 : ℝ) = 1 := map_one _
  repeat rw [hmap_mul]
  repeat rw [hmap_pow]
  try rw [hmap_one]
  rw [hq₁, hq₂]
  ring

theorem normalized_moment_three_eq_eval (q : α → ℝ) (y : κ → S)
    [DecidableEq α] [DecidableEq κ] :
    (1 / 6 : ℝ) • expectation (linearPolynomial (weights q y) ^ 3) =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S (logWeightParameters q i))
        (e₃ (∑ i, y i) (∑ i, y i ^ 2) (∑ i, y i ^ 3)) := by
  rw [normalized_moment_three, eval_e₃]
  have h₀ : logWeightParameters q (0 : Fin 4) = ∑ m, q m := by
    simp [logWeightParameters]
  have h₁ : logWeightParameters q (1 : Fin 4) =
      (1 / 2 : ℝ) * ∑ m, q m ^ 2 := by
    norm_num [logWeightParameters]
    ring
  have h₂ : logWeightParameters q (2 : Fin 4) =
      (1 / 3 : ℝ) * ∑ m, q m ^ 3 := by
    norm_num [logWeightParameters]
    ring
  have hq₁ : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    rw [map_sum]
  have hq₂ : algebraMap ℝ S (∑ m, q m ^ 2) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 2 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  have hq₃ : algebraMap ℝ S (∑ m, q m ^ 3) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 3 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  rw [h₀, h₁, h₂]
  simp only [Algebra.smul_def]
  rw [show (∑ m, q m) ^ 3 / 6 = (∑ m, q m) ^ 3 * (1 / 6 : ℝ) by ring,
    show ((∑ m, q m) * (∑ m, q m ^ 2)) / 2 =
      (∑ m, q m) * (∑ m, q m ^ 2) * (1 / 2 : ℝ) by ring,
    show (∑ m, q m ^ 3) / 3 = (∑ m, q m ^ 3) * (1 / 3 : ℝ) by ring]
  have hmap_mul (a b : ℝ) : algebraMap ℝ S (a * b) =
      algebraMap ℝ S a * algebraMap ℝ S b := by rw [map_mul]
  have hmap_pow (a : ℝ) (n : ℕ) : algebraMap ℝ S (a ^ n) =
      (algebraMap ℝ S a) ^ n := by rw [map_pow]
  have hmap_one : algebraMap ℝ S (1 : ℝ) = 1 := map_one _
  repeat rw [hmap_mul]
  repeat rw [hmap_pow]
  try rw [hmap_one]
  rw [hq₁, hq₂, hq₃]
  ring

theorem normalized_moment_four_eq_eval (q : α → ℝ) (y : κ → S)
    [DecidableEq α] [DecidableEq κ] :
    (1 / 24 : ℝ) • expectation (linearPolynomial (weights q y) ^ 4) =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S (logWeightParameters q i))
        (e₄ (∑ i, y i) (∑ i, y i ^ 2) (∑ i, y i ^ 3) (∑ i, y i ^ 4)) := by
  rw [normalized_moment_four, eval_e₄]
  have h₀ : logWeightParameters q (0 : Fin 4) = ∑ m, q m := by
    simp [logWeightParameters]
  have h₁ : logWeightParameters q (1 : Fin 4) =
      (1 / 2 : ℝ) * ∑ m, q m ^ 2 := by
    norm_num [logWeightParameters]
    ring
  have h₂ : logWeightParameters q (2 : Fin 4) =
      (1 / 3 : ℝ) * ∑ m, q m ^ 3 := by
    norm_num [logWeightParameters]
    ring
  have h₃ : logWeightParameters q (3 : Fin 4) =
      (1 / 4 : ℝ) * ∑ m, q m ^ 4 := by
    norm_num [logWeightParameters]
    ring
  have hq₁ : algebraMap ℝ S (∑ m, q m) = ∑ m, algebraMap ℝ S (q m) := by
    rw [map_sum]
  have hq₂ : algebraMap ℝ S (∑ m, q m ^ 2) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 2 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  have hq₃ : algebraMap ℝ S (∑ m, q m ^ 3) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 3 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  have hq₄ : algebraMap ℝ S (∑ m, q m ^ 4) =
      ∑ m, (algebraMap ℝ S (q m)) ^ 4 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_pow]
  rw [h₀, h₁, h₂, h₃]
  simp only [Algebra.smul_def]
  rw [show (∑ m, q m) ^ 4 / 24 = (∑ m, q m) ^ 4 * (1 / 24 : ℝ) by ring,
    show ((∑ m, q m) ^ 2 * ∑ m, q m ^ 2) / 4 =
      (∑ m, q m) ^ 2 * (∑ m, q m ^ 2) * (1 / 4 : ℝ) by ring,
    show (∑ m, q m ^ 2) ^ 2 / 8 =
      (∑ m, q m ^ 2) ^ 2 * (1 / 8 : ℝ) by ring,
    show ((∑ m, q m) * ∑ m, q m ^ 3) / 3 =
      (∑ m, q m) * (∑ m, q m ^ 3) * (1 / 3 : ℝ) by ring,
    show (∑ m, q m ^ 4) / 4 = (∑ m, q m ^ 4) * (1 / 4 : ℝ) by ring]
  have hmap_mul (a b : ℝ) : algebraMap ℝ S (a * b) =
      algebraMap ℝ S a * algebraMap ℝ S b := by rw [map_mul]
  have hmap_pow (a : ℝ) (n : ℕ) : algebraMap ℝ S (a ^ n) =
      (algebraMap ℝ S a) ^ n := by rw [map_pow]
  have hmap_one : algebraMap ℝ S (1 : ℝ) = 1 := map_one _
  repeat rw [hmap_mul]
  repeat rw [hmap_pow]
  try rw [hmap_one]
  rw [hq₁, hq₂, hq₃, hq₄]
  have hhalf₂ : (algebraMap ℝ S (1 / 2)) ^ 2 = algebraMap ℝ S (1 / 4) := by
    rw [← map_pow]
    norm_num
  have hhalf₃ : (algebraMap ℝ S (1 / 2)) ^ 3 = algebraMap ℝ S (1 / 8) := by
    rw [← map_pow]
    norm_num
  ring_nf
  rw [hhalf₂, hhalf₃]
  ring

theorem fin_weight_logWeightParameters (N : ℕ) (i : Fin 4) :
    logWeightParameters
        (fun m : Fin N => AhatGaussianWeights.weight m.val) i =
      AhatCoefficientLimits.logParameters N i := by
  unfold logWeightParameters AhatCoefficientLimits.logParameters
  change (∑ m : Fin N, AhatGaussianWeights.weight m.val ^ (i.val + 1)) /
      ((i.val : ℝ) + 1) = _
  congr 1
  simpa only using
    (Fin.sum_univ_eq_sum_range
      (fun m : ℕ => AhatGaussianWeights.weight m ^ (i.val + 1)) N)

end
end QuaternionicSymmetry.ComplexGaussianExponentialCoefficients
