import QuaternionicSymmetry.GaussianWick
import QuaternionicSymmetry.CovariancePolynomial

/-!
# The factorial normalization in the PSD-to-orbital comparison

The scalar orbital polynomial is normalized by `(2 * k)!`, whereas a real
Gaussian linear combination has even moment `(2 * k - 1)‼` times the `k`th
power of its variance.  This file proves the exact conversion factor in every
degree, both for the universal polynomial Gaussian expectation and for actual
scalar integrals of a linear functional on a commutative real algebra.

The result is a prerequisite for the PSD-to-orbital mixture.  No symplectic
orbital integral or complex-PSD interpretation is asserted here.
-/

namespace QuaternionicSymmetry.GaussianOrbitalNormalization

open MeasureTheory
open QuaternionicSymmetry.GaussianPolynomialExpectation
open scoped BigOperators ComplexOrder

noncomputable section

/-- The exact conversion between Gaussian Wick normalization and the
`(2k)!` normalization of scalar orbital moments, including `k = 0`. -/
theorem factorial_eq_orbital_wick_factor (k : ℕ) :
    (2 * k).factorial =
      2 ^ k * k.factorial * Nat.doubleFactorial (2 * k - 1) := by
  cases k with
  | zero => norm_num
  | succ k =>
      have h : (2 * (k + 1)).factorial =
          Nat.doubleFactorial (2 * (k + 1)) *
            Nat.doubleFactorial (2 * (k + 1) - 1) := by
        convert Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1) using 1
      rw [Nat.doubleFactorial_two_mul] at h
      exact h

/-- Wick's moment identity with the precise orbital factorial scale.
It holds in every commutative real algebra, including algebras with nilpotents. -/
theorem universal_factorial_wick {ι S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing S] [Algebra ℝ S] (θ : ι → S) (k : ℕ) :
    ((2 ^ k * k.factorial : ℕ) : S) *
        expectation (linearPolynomial θ ^ (2 * k)) =
      ((2 * k).factorial : S) * (∑ i, θ i ^ 2) ^ k := by
  rw [QuaternionicSymmetry.GaussianUniversalWick.even_moment]
  rw [← mul_assoc, ← Nat.cast_mul]
  congr 1
  exact congrArg (fun n : ℕ => (n : S)) (factorial_eq_orbital_wick_factor k).symm

/-- The same normalization for actual finite Gaussian integrals, tested by
an arbitrary real-linear functional. -/
theorem integral_factorial_wick {ι S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing S] [Algebra ℝ S] (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (k : ℕ) :
    ((2 ^ k * k.factorial : ℕ) : ℝ) *
        (∫ ω : ι → ℝ,
          L (GaussianFunctional.combination θ ω ^ (2 * k))
            ∂GaussianWick.standardMeasure) =
      ((2 * k).factorial : ℝ) * L ((∑ i, θ i ^ 2) ^ k) := by
  rw [GaussianWick.integral_combination_even]
  rw [← mul_assoc, ← Nat.cast_mul]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℝ)) (factorial_eq_orbital_wick_factor k).symm

/-- A *numerical* complex PSD matrix has one finite Gaussian Gram factorization
whose normalized Wick identity holds simultaneously in every degree.  The
coefficient algebra `S` can be an algebra of even differential forms: no order
or PSD predicate is imposed on its elements. -/
theorem psd_covariance_universal_wick {κ β S : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
    [CommRing S] [Algebra ℝ S]
    (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian) (η : β → S) :
    ∃ θ : β → S,
      CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
          ∑ s, θ s ^ 2 ∧
      ∀ k : ℕ,
        ((2 ^ k * k.factorial : ℕ) : S) *
            expectation (linearPolynomial θ ^ (2 * k)) =
          ((2 * k).factorial : S) *
            CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η ^ k := by
  obtain ⟨θ, hθ⟩ := CovariancePolynomial.covariance_sum_squares A B hA hB η
  refine ⟨θ, hθ, ?_⟩
  intro k
  rw [hθ]
  exact universal_factorial_wick θ k

/-- The same fixed numerical Gram factorization has the normalized identity
for all degrees and all real-linear scalar evaluations of the coefficient
algebra. -/
theorem psd_covariance_integral_wick {κ β S : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
    [CommRing S] [Algebra ℝ S]
    (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian) (η : β → S) :
    ∃ θ : β → S,
      CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
          ∑ s, θ s ^ 2 ∧
      ∀ (L : S →ₗ[ℝ] ℝ) (k : ℕ),
        ((2 ^ k * k.factorial : ℕ) : ℝ) *
            (∫ ω : β → ℝ,
              L (GaussianFunctional.combination θ ω ^ (2 * k))
                ∂GaussianWick.standardMeasure) =
          ((2 * k).factorial : ℝ) *
            L (CovariancePolynomial.quadratic
              (MatrixMoments.covarianceMatrix A B) η ^ k) := by
  obtain ⟨θ, hθ⟩ := CovariancePolynomial.covariance_sum_squares A B hA hB η
  refine ⟨θ, hθ, ?_⟩
  intro L k
  rw [hθ]
  exact integral_factorial_wick L θ k

end
end QuaternionicSymmetry.GaussianOrbitalNormalization
