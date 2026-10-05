import Mathlib.Topology.Algebra.MvPolynomial
import QuaternionicSymmetry.AhatGaussianWeights
import QuaternionicSymmetry.AlgebraPolynomialLimits

/-! Finite exponential coefficients built from the partial logarithmic
parameters.  The limits here are polynomial identities over an arbitrary
real algebra; they do not identify these coefficients with geometric or
Gaussian moments. -/

namespace QuaternionicSymmetry.AhatCoefficientLimits

open Filter Topology

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S]

local notation "s(" r ")" => algebraMap ℝ S r

def e₂ (z₁ z₂ : S) : MvPolynomial (Fin 4) S :=
  MvPolynomial.C z₂ * MvPolynomial.X 1
    + MvPolynomial.C (s(1 / 2) * z₁ ^ 2) * (MvPolynomial.X 0) ^ 2

def e₃ (z₁ z₂ z₃ : S) : MvPolynomial (Fin 4) S :=
  MvPolynomial.C z₃ * MvPolynomial.X 2
    + MvPolynomial.C (z₁ * z₂) * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C (s(1 / 6) * z₁ ^ 3) * (MvPolynomial.X 0) ^ 3

def e₄ (z₁ z₂ z₃ z₄ : S) : MvPolynomial (Fin 4) S :=
  MvPolynomial.C z₄ * MvPolynomial.X 3
    + MvPolynomial.C (z₁ * z₃) * MvPolynomial.X 0 * MvPolynomial.X 2
    + MvPolynomial.C (s(1 / 2) * z₂ ^ 2) * (MvPolynomial.X 1) ^ 2
    + MvPolynomial.C (s(1 / 2) * z₁ ^ 2 * z₂) * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1
    + MvPolynomial.C (s(1 / 24) * z₁ ^ 4) * (MvPolynomial.X 0) ^ 4

def logParameters (N : ℕ) (i : Fin 4) : ℝ :=
  (∑ m ∈ Finset.range N, AhatGaussianWeights.weight m ^ (i.val + 1)) /
    ((i.val : ℝ) + 1)

def logLimit (i : Fin 4) : ℝ := AhatGaussianWeights.positiveLog (i.val + 1)

theorem logParameters_tendsto (i : Fin 4) :
    Tendsto (fun N => logParameters N i) atTop (𝓝 (logLimit i)) := by
  convert (AhatGaussianWeights.partial_log_tendsto (j := i.val + 1) (by omega)) using 1 ;
    norm_num [logParameters]

theorem eval_e₂ (z₁ z₂ : S) (a : Fin 4 → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (a i)) (e₂ z₁ z₂) =
      algebraMap ℝ S (a 1) * z₂ +
        algebraMap ℝ S (1 / 2) * (algebraMap ℝ S (a 0)) ^ 2 * z₁ ^ 2 := by
  simp only [e₂, map_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow]
  ring

theorem eval_e₃ (z₁ z₂ z₃ : S) (a : Fin 4 → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (a i)) (e₃ z₁ z₂ z₃) =
      algebraMap ℝ S (a 2) * z₃ +
        algebraMap ℝ S (a 0) * algebraMap ℝ S (a 1) * z₁ * z₂ +
        algebraMap ℝ S (1 / 6) * (algebraMap ℝ S (a 0)) ^ 3 * z₁ ^ 3 := by
  simp only [e₃, map_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow]
  ring

theorem eval_e₄ (z₁ z₂ z₃ z₄ : S) (a : Fin 4 → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (a i)) (e₄ z₁ z₂ z₃ z₄) =
      algebraMap ℝ S (a 3) * z₄ +
        algebraMap ℝ S (a 0) * algebraMap ℝ S (a 2) * z₁ * z₃ +
        algebraMap ℝ S (1 / 2) * (algebraMap ℝ S (a 1)) ^ 2 * z₂ ^ 2 +
        algebraMap ℝ S (1 / 2) * (algebraMap ℝ S (a 0)) ^ 2 *
            algebraMap ℝ S (a 1) * z₁ ^ 2 * z₂ +
        algebraMap ℝ S (1 / 24) * (algebraMap ℝ S (a 0)) ^ 4 * z₁ ^ 4 := by
  simp only [e₄, map_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow]
  ring_nf

theorem e₂_limit_eval (z₁ z₂ : S) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (logLimit i)) (e₂ z₁ z₂) =
      algebraMap ℝ S (1 / 1152) * z₁ ^ 2 + algebraMap ℝ S (1 / 2880) * z₂ := by
  rw [eval_e₂]
  simp only [logLimit]
  norm_num
  have hc : algebraMap ℝ S (1 / 2) * (algebraMap ℝ S (1 / 24)) ^ 2 =
      algebraMap ℝ S (1 / 1152) := by
    rw [← map_pow, ← map_mul]
    norm_num
  linear_combination z₁ ^ 2 * hc

theorem e₃_limit_eval (z₁ z₂ z₃ : S) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (logLimit i)) (e₃ z₁ z₂ z₃) =
      algebraMap ℝ S (1 / 82944) * z₁ ^ 3 +
        algebraMap ℝ S (1 / 69120) * z₁ * z₂ +
        algebraMap ℝ S (1 / 181440) * z₃ := by
  rw [eval_e₃]
  simp only [logLimit]
  norm_num
  have hc₁ : algebraMap ℝ S (1 / 24) * algebraMap ℝ S (1 / 2880) =
      algebraMap ℝ S (1 / 69120) := by
    rw [← map_mul]
    norm_num
  have hc₂ : (algebraMap ℝ S (1 / 24)) ^ 3 * algebraMap ℝ S (1 / 6) =
      algebraMap ℝ S (1 / 82944) := by
    rw [← map_pow, ← map_mul]
    norm_num
  linear_combination z₁ * z₂ * hc₁ + z₁ ^ 3 * hc₂

theorem e₄_limit_eval (z₁ z₂ z₃ z₄ : S) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (logLimit i)) (e₄ z₁ z₂ z₃ z₄) =
      algebraMap ℝ S (1 / 7962624) * z₁ ^ 4 +
        algebraMap ℝ S (1 / 3317760) * z₁ ^ 2 * z₂ +
        algebraMap ℝ S (1 / 16588800) * z₂ ^ 2 +
        algebraMap ℝ S (1 / 4354560) * z₁ * z₃ +
        algebraMap ℝ S (1 / 9676800) * z₄ := by
  rw [eval_e₄]
  simp only [logLimit]
  norm_num
  have hc₁ : algebraMap ℝ S (1 / 24) * algebraMap ℝ S (1 / 181440) =
      algebraMap ℝ S (1 / 4354560) := by
    rw [← map_mul]
    norm_num
  have hc₂ : (algebraMap ℝ S (1 / 24)) ^ 2 * algebraMap ℝ S (1 / 2) *
      algebraMap ℝ S (1 / 2880) = algebraMap ℝ S (1 / 3317760) := by
    rw [← map_pow, ← map_mul, ← map_mul]
    norm_num
  have hc₃ : algebraMap ℝ S (1 / 2) * (algebraMap ℝ S (1 / 2880)) ^ 2 =
      algebraMap ℝ S (1 / 16588800) := by
    rw [← map_pow, ← map_mul]
    norm_num
  have hc₄ : (algebraMap ℝ S (1 / 24)) ^ 5 =
      algebraMap ℝ S (1 / 7962624) := by
    rw [← map_pow]
    norm_num
  linear_combination z₁ * z₃ * hc₁ + z₁ ^ 2 * z₂ * hc₂ +
    z₂ ^ 2 * hc₃ + z₁ ^ 4 * hc₄

theorem scalar_e₂_tendsto (z₁ z₂ : S) (L : S →ₗ[ℝ] ℝ) :
    Tendsto
      (fun N => L (MvPolynomial.eval
        (fun i => algebraMap ℝ S (logParameters N i)) (e₂ z₁ z₂)))
      atTop
      (𝓝 (L (algebraMap ℝ S (1 / 1152) * z₁ ^ 2 +
        algebraMap ℝ S (1 / 2880) * z₂))) := by
  have h := AlgebraPolynomialLimits.scalar_eval_tendsto (e₂ z₁ z₂) L
    logParameters logLimit logParameters_tendsto
  rw [e₂_limit_eval] at h
  exact h

theorem scalar_e₃_tendsto (z₁ z₂ z₃ : S) (L : S →ₗ[ℝ] ℝ) :
    Tendsto
      (fun N => L (MvPolynomial.eval
        (fun i => algebraMap ℝ S (logParameters N i)) (e₃ z₁ z₂ z₃)))
      atTop
      (𝓝 (L (algebraMap ℝ S (1 / 82944) * z₁ ^ 3 +
        algebraMap ℝ S (1 / 69120) * z₁ * z₂ +
        algebraMap ℝ S (1 / 181440) * z₃))) := by
  have h := AlgebraPolynomialLimits.scalar_eval_tendsto (e₃ z₁ z₂ z₃) L
    logParameters logLimit logParameters_tendsto
  rw [e₃_limit_eval] at h
  exact h

theorem scalar_e₄_tendsto (z₁ z₂ z₃ z₄ : S) (L : S →ₗ[ℝ] ℝ) :
    Tendsto
      (fun N => L (MvPolynomial.eval
        (fun i => algebraMap ℝ S (logParameters N i)) (e₄ z₁ z₂ z₃ z₄)))
      atTop
      (𝓝 (L (algebraMap ℝ S (1 / 7962624) * z₁ ^ 4 +
        algebraMap ℝ S (1 / 3317760) * z₁ ^ 2 * z₂ +
        algebraMap ℝ S (1 / 16588800) * z₂ ^ 2 +
        algebraMap ℝ S (1 / 4354560) * z₁ * z₃ +
        algebraMap ℝ S (1 / 9676800) * z₄))) := by
  have h := AlgebraPolynomialLimits.scalar_eval_tendsto
    (e₄ z₁ z₂ z₃ z₄) L logParameters logLimit logParameters_tendsto
  rw [e₄_limit_eval] at h
  exact h

end
end QuaternionicSymmetry.AhatCoefficientLimits
