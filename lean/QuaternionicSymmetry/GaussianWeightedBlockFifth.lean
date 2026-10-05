import QuaternionicSymmetry.GaussianWeightedBlockMoments
import QuaternionicSymmetry.FifthGaussianMatrixMoment
import QuaternionicSymmetry.AhatFifthCoefficientLimits

/-! The fifth normalized moment of the finite weighted Gaussian matrix is the
fifth exponential coefficient, including its normalization by `5!`. -/

namespace QuaternionicSymmetry.GaussianWeightedBlockFifth

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable {α κ S : Type*} [Fintype α] [DecidableEq α]
  [Fintype κ] [DecidableEq κ] [CommRing S] [Algebra ℂ S]

def logWeightParameters (q : α → ℝ) (i : Fin 5) : ℝ :=
  (∑ m, q m ^ (i.val + 1)) / ((i.val : ℝ) + 1)

theorem fin_weight_logWeightParameters (N : ℕ) (i : Fin 5) :
    logWeightParameters
        (fun m : Fin N => AhatGaussianWeights.weight m.val) i =
      AhatFifthCoefficientLimits.logParameters N i := by
  unfold logWeightParameters AhatFifthCoefficientLimits.logParameters
  congr 1
  simpa only using
    (Fin.sum_univ_eq_sum_range
      (fun m : ℕ => AhatGaussianWeights.weight m ^ (i.val + 1)) N)

private theorem trace_block (q : α → ℝ) (Y : Matrix κ κ S) :
    Matrix.trace (WeightedBlockMatrix.block q Y) =
      (∑ m, algebraMap ℝ S (q m)) * Matrix.trace Y := by
  simpa only [pow_one] using WeightedBlockMatrix.trace_block_pow q Y 1

theorem normalized_moment_five_eq_eval (q : α → ℝ) (Y : Matrix κ κ S) :
    (1 / 120 : ℝ) • GaussianMatrixTracePolynomial.moment q Y 5 =
      MvPolynomial.eval
        (fun i => algebraMap ℝ S (logWeightParameters q i))
        (AhatFifthCoefficientLimits.e₅ (Matrix.trace Y) (Matrix.trace (Y ^ 2))
          (Matrix.trace (Y ^ 3)) (Matrix.trace (Y ^ 4)) (Matrix.trace (Y ^ 5))) := by
  rw [GaussianWeightedBlockMoments.moment_eq_block,
    FifthGaussianMatrixMoment.moment_five,
    AhatFifthCoefficientLimits.eval_e₅]
  simp only [trace_block,
    WeightedBlockMatrix.trace_block_pow]
  norm_num [logWeightParameters]
  simp only [Algebra.smul_def, div_eq_mul_inv, map_mul, map_pow, map_sum, one_mul]
  set a : S := ∑ m, algebraMap ℝ S (q m)
  set b : S := ∑ m, algebraMap ℝ S (q m) ^ 2
  set c : S := ∑ m, algebraMap ℝ S (q m) ^ 3
  set d : S := ∑ m, algebraMap ℝ S (q m) ^ 4
  set e : S := ∑ m, algebraMap ℝ S (q m) ^ 5
  set x : S := Matrix.trace Y
  set y : S := Matrix.trace (Y ^ 2)
  set z : S := Matrix.trace (Y ^ 3)
  set w : S := Matrix.trace (Y ^ 4)
  set v : S := Matrix.trace (Y ^ 5)
  have h15 : algebraMap ℝ S (1 / 8) = 15 * algebraMap ℝ S (1 / 120) := by
    calc
      _ = algebraMap ℝ S (15 * (1 / 120)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h20 : algebraMap ℝ S (1 / 2) * algebraMap ℝ S (1 / 3) =
      20 * algebraMap ℝ S (1 / 120) := by
    rw [← map_mul]
    calc
      _ = algebraMap ℝ S (20 * (1 / 120)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h10 : algebraMap ℝ S (1 / 2) * algebraMap ℝ S (1 / 6) =
      10 * algebraMap ℝ S (1 / 120) := by
    rw [← map_mul]
    calc
      _ = algebraMap ℝ S (10 * (1 / 120)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h30 : algebraMap ℝ S (1 / 4) = 30 * algebraMap ℝ S (1 / 120) := by
    calc
      _ = algebraMap ℝ S (30 * (1 / 120)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  have h24 : algebraMap ℝ S (1 / 5) = 24 * algebraMap ℝ S (1 / 120) := by
    calc
      _ = algebraMap ℝ S (24 * (1 / 120)) := by norm_num
      _ = _ := by rw [map_mul, map_ofNat]
  simp only [one_div] at *
  have h15' : (algebraMap ℝ S (2⁻¹ : ℝ)) ^ 3 =
      15 * algebraMap ℝ S (120⁻¹ : ℝ) := by
    rw [← map_pow]
    convert h15 using 1; norm_num
  linear_combination -(a * b ^ 2 * x * y ^ 2) * h15' -
    (a ^ 2 * c * x ^ 2 * z) * h20 -
    (b * c * y * z) * h20 -
    (a ^ 3 * b * x ^ 3 * y) * h10 -
    (a * d * x * w) * h30 -
    (e * v) * h24

end
end QuaternionicSymmetry.GaussianWeightedBlockFifth
