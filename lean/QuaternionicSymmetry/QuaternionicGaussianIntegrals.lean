import QuaternionicSymmetry.QuaternionicGaussianMoments
import QuaternionicSymmetry.GaussianFunctionalPolynomial

/-! Actual scalar Gaussian integrals of the polynomial quaternionic moments. -/

set_option maxHeartbeats 800000

namespace QuaternionicSymmetry.QuaternionicGaussianIntegrals

open Module QuaternionicFundamental
open MeasureTheory
open scoped BigOperators ComplexOrder

noncomputable section

variable {δ ι κ β V : Type*} [Fintype δ] [Fintype ι] [Fintype κ]
  [DecidableEq κ] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [DecidableEq β] [DecidableEq κ] [FiniteDimensional ℝ V] in
theorem integrable_mixed (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (k : ℕ) (L : E V →ₗ[ℝ] ℝ) :
    Integrable (fun x : δ → ℝ =>
      L ((-CovariancePolynomial.quadratic
        (MatrixMoments.covarianceMatrix (PolynomialCovariance.evalMatrix A x) B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)))
      GaussianFunctionalPolynomial.standardMeasure := by
  let p : MvPolynomial δ (E V) :=
    MvPolynomial.C (QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) *
      PolynomialCovariance.expression A B η ^ k
  have h := GaussianFunctionalPolynomial.polynomial_integrable L p
  rw [show
      (fun x : δ → ℝ => L ((-CovariancePolynomial.quadratic
        (MatrixMoments.covarianceMatrix (PolynomialCovariance.evalMatrix A x) B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))) =
      (fun x : δ → ℝ => L (p.eval (fun i => algebraMap ℝ (E V) (x i)))) by
        funext x
        simp only [p, map_mul, MvPolynomial.eval_C, map_pow,
          PolynomialCovariance.eval_expression]
        rw [mul_comm]]
  exact h

omit [DecidableEq β] [DecidableEq κ] [FiniteDimensional ℝ V] in
theorem integral_mixed (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (k : ℕ) (L : E V →ₗ[ℝ] ℝ) :
    (∫ x : δ → ℝ,
      L ((-CovariancePolynomial.quadratic
        (MatrixMoments.covarianceMatrix (PolynomialCovariance.evalMatrix A x) B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))
      ∂GaussianFunctionalPolynomial.standardMeasure) =
      L (QuaternionicGaussianMoments.moment A B η k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  let p : MvPolynomial δ (E V) :=
    MvPolynomial.C (QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) *
      PolynomialCovariance.expression A B η ^ k
  have h := GaussianFunctionalPolynomial.integral_polynomial L p
  rw [GaussianAffineMoments.expectation_C_mul] at h
  rw [show
      (fun x : δ → ℝ => L ((-CovariancePolynomial.quadratic
        (MatrixMoments.covarianceMatrix (PolynomialCovariance.evalMatrix A x) B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))) =
      (fun x : δ → ℝ => L (p.eval (fun i => algebraMap ℝ (E V) (x i)))) by
        funext x
        simp only [p, map_mul, MvPolynomial.eval_C, map_pow,
          PolynomialCovariance.eval_expression]
        rw [mul_comm]]
  simpa [p, QuaternionicGaussianMoments.moment, mul_comm] using h

theorem integral_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (hA : ∀ x : δ → ℝ,
      (PolynomialCovariance.evalMatrix A x).PosSemidef)
    (hB : ∀ b, (B b).IsHermitian) (η : β → E V)
    (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (L : E V →ₗ[ℝ] ℝ)
    (hvol : 0 ≤ L (QuaternionicFundamental.topForm Q c)) :
    0 ≤ (∫ x : δ → ℝ,
      L ((-CovariancePolynomial.quadratic
        (MatrixMoments.covarianceMatrix (PolynomialCovariance.evalMatrix A x) B) η) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))
      ∂GaussianFunctionalPolynomial.standardMeasure) := by
  apply integral_nonneg
  intro x
  exact QuaternionicMomentPositivity.covariance_mixed_nonneg Q c
    (PolynomialCovariance.evalMatrix A x) B (hA x) hB η hη k hk L hvol

end
end QuaternionicSymmetry.QuaternionicGaussianIntegrals
