import QuaternionicSymmetry.CovariancePolynomial
import QuaternionicSymmetry.GaussianWick

/-! From a spectral sign on a real subspace to matrix moment positivity.

The spectral sign is an explicit hypothesis here. This file proves the full
Gram factorization and Gaussian averaging implication, including mixed terms;
it does not assume an order on the coefficient algebra.
-/

namespace QuaternionicSymmetry.MatrixMomentPositivity

open scoped BigOperators ComplexOrder

noncomputable section

variable {S β ι : Type*} [CommRing S] [Algebra ℝ S]
    [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

private def signedFunctional (L : S →ₗ[ℝ] ℝ) (k : ℕ) : S →ₗ[ℝ] ℝ :=
  L.comp (LinearMap.mulLeft ℝ ((-1 : S) ^ k))

private theorem signed_pow (L : S →ₗ[ℝ] ℝ) (k : ℕ) (x : S) :
    signedFunctional L k (x ^ k) = L ((-x) ^ k) := by
  change L ((-1) ^ k * x ^ k) = L ((-x) ^ k)
  rw [neg_pow x k]

private theorem signed_even_pow (L : S →ₗ[ℝ] ℝ) (k : ℕ) (x : S) :
    signedFunctional L k (x ^ (2 * k)) = L ((-(x ^ 2)) ^ k) := by
  rw [pow_mul]
  exact signed_pow L k (x ^ 2)

/-- Gaussian averaging preserves the spectral sign across all mixed products. -/
theorem negative_sum_squares_power_nonneg (W : Submodule ℝ S) (L : S →ₗ[ℝ] ℝ)
    (k : ℕ) (hSpectral : ∀ x ∈ W, 0 ≤ L ((-(x ^ 2)) ^ k))
    (θ : β → S) (hθ : ∀ b, θ b ∈ W) :
    0 ≤ L ((-(∑ b, θ b ^ 2)) ^ k) := by
  have h := GaussianWick.sum_squares_power_nonneg (signedFunctional L k) θ k
    (fun t => by
      rw [signed_even_pow]
      apply hSpectral
      exact W.sum_mem fun b _ => W.smul_mem (t b) (hθ b))
  rwa [signed_pow] at h

/-- Numerical positive semidefiniteness and a spectral sign imply the covariance moment sign. -/
theorem covariance_power_nonneg (W : Submodule ℝ S) (L : S →ₗ[ℝ] ℝ)
    (k : ℕ) (hSpectral : ∀ x ∈ W, 0 ≤ L ((-(x ^ 2)) ^ k))
    (A : Matrix ι ι ℂ) (B : β → Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian)
    (η : β → S) (hη : ∀ b, η b ∈ W) :
    0 ≤ L ((-CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η) ^ k) := by
  obtain ⟨C, hC⟩ := MatrixMoments.covarianceMatrix_factorization A B hA hB
  rw [hC, CovariancePolynomial.gram_quadratic]
  apply negative_sum_squares_power_nonneg W L k hSpectral
  intro b
  apply W.sum_mem
  intro a _
  rw [← Algebra.smul_def]
  exact W.smul_mem _ (hη a)

end
end QuaternionicSymmetry.MatrixMomentPositivity
