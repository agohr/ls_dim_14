import QuaternionicSymmetry.QuaternionicSpectralSign
import QuaternionicSymmetry.MatrixMomentPositivity
import QuaternionicSymmetry.PositiveRay

/-! Matrix moment positivity for the actual quaternionic exterior form space. -/

namespace QuaternionicSymmetry.QuaternionicMomentPositivity

open Module QuaternionicFundamental
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι V β κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private def mixedFunctional (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (k : ℕ) (L : E V →ₗ[ℝ] ℝ) : E V →ₗ[ℝ] ℝ :=
  L.comp (LinearMap.mulLeft ℝ (QuaternionicFundamental.form Q c ^
    (Q.quaternionicDimension - k)))

omit [DecidableEq ι] in
private theorem mixedFunctional_spectral (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (L : E V →ₗ[ℝ] ℝ)
    (hvol : 0 ≤ L (QuaternionicFundamental.topForm Q c)) :
    ∀ x ∈ HyperholomorphicExterior.formSpace Q c,
      0 ≤ mixedFunctional Q c k L ((-(x ^ 2)) ^ k) := by
  intro x hx
  change 0 ≤ L (QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k) *
    (-(x ^ 2)) ^ k)
  rw [mul_comm]
  exact QuaternionicSpectralSign.formSpace_signed_mixed_nonneg Q c x hx k hk L hvol

omit [DecidableEq ι] in
theorem negative_sum_squares_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (θ : β → E V) (hθ : ∀ b, θ b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (L : E V →ₗ[ℝ] ℝ)
    (hvol : 0 ≤ L (QuaternionicFundamental.topForm Q c)) :
    0 ≤ L ((-(∑ b, θ b ^ 2)) ^ k * QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) := by
  have h := MatrixMomentPositivity.negative_sum_squares_power_nonneg
    (HyperholomorphicExterior.formSpace Q c) (mixedFunctional Q c k L) k
    (mixedFunctional_spectral Q c k hk L hvol) θ hθ
  change 0 ≤ L (QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k) *
    (-(∑ b, θ b ^ 2)) ^ k) at h
  rw [mul_comm]
  exact h

omit [DecidableEq ι] in
theorem covariance_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (L : E V →ₗ[ℝ] ℝ)
    (hvol : 0 ≤ L (QuaternionicFundamental.topForm Q c)) :
    0 ≤ L ((-CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η) ^ k *
      QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  have h := MatrixMomentPositivity.covariance_power_nonneg
    (HyperholomorphicExterior.formSpace Q c) (mixedFunctional Q c k L) k
    (mixedFunctional_spectral Q c k hk L hvol) A B hA hB η hη
  change 0 ≤ L (QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k) *
    (-CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η) ^ k) at h
  rw [mul_comm]
  exact h

omit [DecidableEq ι] in
theorem negative_sum_squares_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (θ : β → E V)
    (hθ : ∀ b, θ b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (QuaternionicFundamental.topForm Q c)
      ((-(∑ b, θ b ^ 2)) ^ k * QuaternionicFundamental.form Q c ^
        (Q.quaternionicDimension - k)) := by
  apply (PositiveRay.contains_iff_functional_nonneg
    (QuaternionicSpectralSign.topForm_ne_zero Q c)).mpr
  intro L hL
  exact negative_sum_squares_mixed_nonneg Q c θ hθ k hk L hL

omit [DecidableEq ι] in
theorem covariance_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (QuaternionicFundamental.topForm Q c)
      ((-CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  apply (PositiveRay.contains_iff_functional_nonneg
    (QuaternionicSpectralSign.topForm_ne_zero Q c)).mpr
  intro L hL
  exact covariance_mixed_nonneg Q c A B hA hB η hη k hk L hL

end
end QuaternionicSymmetry.QuaternionicMomentPositivity
