import QuaternionicSymmetry.PolynomialCovariance
import QuaternionicSymmetry.QuaternionicMomentPositivity
import QuaternionicSymmetry.GaussianPositiveRay

/-! Gaussian averaging of polynomial positive semidefinite matrices gives
genuine nonnegative quaternionic top forms. -/

namespace QuaternionicSymmetry.QuaternionicGaussianMoments

open Module QuaternionicFundamental
open scoped ComplexOrder

noncomputable section

variable {δ ι κ β V : Type*} [Fintype δ] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def moment (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (k : ℕ) : E V :=
  GaussianPolynomialExpectation.expectation (PolynomialCovariance.expression A B η ^ k)

theorem moment_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (hA : ∀ x : δ → ℝ, (PolynomialCovariance.evalMatrix A x).PosSemidef)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (moment A B η k * form Q c ^ (Q.quaternionicDimension - k)) := by
  have h := GaussianPositiveRay.expectation_contains
    (QuaternionicSpectralSign.topForm_ne_zero Q c)
    (p := MvPolynomial.C (form Q c ^ (Q.quaternionicDimension - k)) *
      PolynomialCovariance.expression A B η ^ k) (fun x => ?_)
  · rw [GaussianAffineMoments.expectation_C_mul] at h
    change PositiveRay.Contains (topForm Q c)
      (form Q c ^ (Q.quaternionicDimension - k) * moment A B η k) at h
    rw [mul_comm] at h
    exact h
  · rw [map_mul, MvPolynomial.eval_C, map_pow, PolynomialCovariance.eval_expression]
    rw [mul_comm]
    exact QuaternionicMomentPositivity.covariance_mixed_in_positive_ray Q c
      (PolynomialCovariance.evalMatrix A x) B (hA x) hB η hη k hk

end
end QuaternionicSymmetry.QuaternionicGaussianMoments
