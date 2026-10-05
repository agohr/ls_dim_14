import QuaternionicSymmetry.GaussianQuadraticPolynomial
import QuaternionicSymmetry.ComplexGaussianRankOne
import QuaternionicSymmetry.MatrixValuedForms
import QuaternionicSymmetry.GaussianPositiveRay
import QuaternionicSymmetry.GaussianAffineMoments

/-! Actual evaluations of the Gaussian quadratic polynomial are rank-one
matrix traces, also with coefficients in a commutative complex algebra. -/

namespace QuaternionicSymmetry.GaussianQuadraticTrace

open Matrix
open scoped BigOperators

noncomputable section

variable {κ S : Type*} [Fintype κ] [CommRing S] [Algebra ℂ S]

theorem trace_rankOne_mul (v : κ → ℂ) (Y : Matrix κ κ S) :
    Matrix.trace ((ComplexGaussianRankOne.rankOne v).map (algebraMap ℂ S) * Y) =
      ∑ i, ∑ j, algebraMap ℂ S (star (v i)) * Y i j * algebraMap ℂ S (v j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply,
    ComplexGaussianRankOne.rankOne_apply, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem eval_quadratic (Y : Matrix κ κ S) (ω : (κ × Fin 2) → ℝ) :
    (GaussianQuadraticPolynomial.quadratic Y).eval (fun p => algebraMap ℝ S (ω p)) =
      Matrix.trace ((ComplexGaussianRankOne.rankOne
        (fun i => ComplexGaussianVariable.standardComplex (fun a => ω (i, a)))).map
          (algebraMap ℂ S) * Y) := by
  rw [GaussianQuadraticPolynomial.eval_quadratic, trace_rankOne_mul]

theorem moment_mul_contains {v w : S} (hv : v ≠ 0) (Y : Matrix κ κ S) (k : ℕ)
    (h : ∀ z : κ → ℂ, PositiveRay.Contains v
      (Matrix.trace ((ComplexGaussianRankOne.rankOne z).map (algebraMap ℂ S) * Y) ^ k * w)) :
    PositiveRay.Contains v (GaussianQuadraticPolynomial.moment Y k * w) := by
  have hp := GaussianPositiveRay.expectation_contains hv
    (MvPolynomial.C w * GaussianQuadraticPolynomial.quadratic Y ^ k) ?_
  · rw [GaussianAffineMoments.expectation_C_mul] at hp
    change PositiveRay.Contains v (w * GaussianQuadraticPolynomial.moment Y k) at hp
    rwa [mul_comm w] at hp
  · intro x
    rw [map_mul, MvPolynomial.eval_C, map_pow, eval_quadratic, mul_comm w]
    exact h _

theorem scaled_moment_mul_contains {v w : S} (hv : v ≠ 0)
    (Y : Matrix κ κ S) (k : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ z : κ → ℂ, PositiveRay.Contains v
      (Matrix.trace ((ComplexGaussianRankOne.rankOne z).map (algebraMap ℂ S) * Y) ^ k * w)) :
    PositiveRay.Contains v (r • GaussianQuadraticPolynomial.moment Y k * w) := by
  rw [Algebra.smul_mul_assoc]
  exact PositiveRay.smul (moment_mul_contains hv Y k h) hr

end
end QuaternionicSymmetry.GaussianQuadraticTrace
