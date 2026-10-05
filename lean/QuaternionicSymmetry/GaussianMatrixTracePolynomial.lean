import QuaternionicSymmetry.ComplexGaussianMatrix
import QuaternionicSymmetry.GaussianQuadraticTrace
import QuaternionicSymmetry.GaussianPositiveRay
import QuaternionicSymmetry.GaussianAffineMoments

/-! Traces against the actual finite weighted Gaussian covariance matrix,
expressed as polynomials in its independent real coordinates. -/

namespace QuaternionicSymmetry.GaussianMatrixTracePolynomial

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable {α κ S : Type*} [Fintype α] [Fintype κ]
  [CommRing S] [Algebra ℂ S]

def tracePolynomial (q : α → ℝ) (Y : Matrix κ κ S) :
    MvPolynomial ((α × κ) × Fin 2) S :=
  Matrix.trace ((ComplexGaussianMatrix.matrixPolynomial q).map
    (MvPolynomial.map (algebraMap ℂ S)) * Y.map MvPolynomial.C)

def moment (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ) : S :=
  GaussianPolynomialExpectation.expectation (tracePolynomial q Y ^ k)

theorem eval_tracePolynomial (q : α → ℝ) (Y : Matrix κ κ S)
    (x : ((α × κ) × Fin 2) → ℝ) :
    (tracePolynomial q Y).eval (fun p => algebraMap ℝ S (x p)) =
      Matrix.trace ((PolynomialCovariance.evalMatrix
        (ComplexGaussianMatrix.matrixPolynomial q) x).map (algebraMap ℂ S) * Y) := by
  unfold tracePolynomial
  rw [AddMonoidHom.map_trace, Matrix.map_mul]
  apply congrArg Matrix.trace
  congr 1
  · ext i j
    simp only [Matrix.map_apply, MvPolynomial.eval_map,
      PolynomialCovariance.evalMatrix]
    exact (MvPolynomial.eval₂_comp (algebraMap ℂ S) (fun p => (x p : ℂ)) _).symm
  · ext i j
    simp

theorem moment_mul_contains {v w : S} (hv : v ≠ 0)
    (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ)
    (h : ∀ x : ((α × κ) × Fin 2) → ℝ,
      PositiveRay.Contains v
        (Matrix.trace ((PolynomialCovariance.evalMatrix
          (ComplexGaussianMatrix.matrixPolynomial q) x).map (algebraMap ℂ S) * Y) ^ k * w)) :
    PositiveRay.Contains v (moment q Y k * w) := by
  have hp := GaussianPositiveRay.expectation_contains hv
    (MvPolynomial.C w * tracePolynomial q Y ^ k) ?_
  · rw [GaussianAffineMoments.expectation_C_mul] at hp
    change PositiveRay.Contains v (w * moment q Y k) at hp
    rwa [mul_comm w] at hp
  · intro x
    rw [map_mul, MvPolynomial.eval_C, map_pow, eval_tracePolynomial, mul_comm w]
    exact h x

theorem normalized_moment_mul_contains {v w : S} (hv : v ≠ 0)
    (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ)
    (h : ∀ x : ((α × κ) × Fin 2) → ℝ,
      PositiveRay.Contains v
        (Matrix.trace ((PolynomialCovariance.evalMatrix
          (ComplexGaussianMatrix.matrixPolynomial q) x).map (algebraMap ℂ S) * Y) ^ k * w)) :
    PositiveRay.Contains v (((k.factorial : ℝ)⁻¹) • moment q Y k * w) := by
  rw [Algebra.smul_mul_assoc]
  exact PositiveRay.smul (moment_mul_contains hv q Y k h) (by positivity)

end
end QuaternionicSymmetry.GaussianMatrixTracePolynomial
