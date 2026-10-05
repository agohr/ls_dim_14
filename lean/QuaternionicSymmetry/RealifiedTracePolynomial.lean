import QuaternionicSymmetry.ComplexMatrixRealificationAlgebra
import QuaternionicSymmetry.MatrixTracePolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! Complex half traces equal realified quarter traces as polynomial
identities, and hence after substitution into any real coefficient algebra. -/
namespace QuaternionicSymmetry.RealifiedTracePolynomial
open MatrixTracePolynomial ComplexMatrixRealification ComplexMatrixRealificationAlgebra
noncomputable section
variable {β κ R : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]
  [CommRing R] [Algebra ℝ R]

def combination (B : β → Matrix κ κ ℝ) (η : β → R) : Matrix κ κ R :=
  fun i j => ∑ b, algebraMap ℝ R (B b i j) * η b

def polynomial (B : β → Matrix κ κ ℝ) : Matrix κ κ (MvPolynomial β ℝ) :=
  combination B MvPolynomial.X

theorem aeval_polynomial (B : β → Matrix κ κ ℝ) (η : β → R) :
    (MvPolynomial.aeval η).toRingHom.mapMatrix (polynomial B) = combination B η := by
  ext i j
  simp [polynomial, combination]

theorem aeval_trace_polynomial_pow (B : β → Matrix κ κ ℝ) (η : β → R) (k : ℕ) :
    MvPolynomial.aeval η (Matrix.trace (polynomial B ^ k)) =
      Matrix.trace (combination B η ^ k) := by
  rw [AddMonoidHom.map_trace]
  change Matrix.trace ((MvPolynomial.aeval η).toRingHom.mapMatrix (polynomial B ^ k)) = _
  rw [map_pow, aeval_polynomial]

omit [Fintype κ] [DecidableEq κ] in
theorem realify_matrixCombination (A : β → Matrix κ κ ℂ) (x : β → ℝ) :
    realify (matrixCombination A x) = combination (fun b => realify (A b)) x := by
  change realifyLinear (matrixCombination A x) = _
  unfold matrixCombination
  simp only [Complex.coe_smul, map_sum, map_smul]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, combination]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem tracePowerPolynomial_eq_realified (A : β → Matrix κ κ ℂ) (j : ℕ) :
    tracePowerPolynomial A j = MvPolynomial.C (1 / 4 : ℝ) *
      Matrix.trace (polynomial (fun b => realify (A b)) ^ (2 * j)) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_tracePowerPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have he := aeval_trace_polynomial_pow (fun b => realify (A b)) x (2 * j)
  change MvPolynomial.eval x _ = _ at he
  rw [he, ← realify_matrixCombination, ← realify_pow, trace_realify]
  unfold CompactSymplecticTraceInvariants.evenTracePower
  ring

theorem signedTracePower_eq_realified (A : β → Matrix κ κ ℂ) (η : β → R) (j : ℕ) :
    signedTracePower (complexifiedMatrix A η) j =
      ((-1 : ℝ) ^ j / 4) • Matrix.trace (combination (fun b => realify (A b)) η ^ (2 * j)) := by
  have h := congrArg (MvPolynomial.aeval η) (tracePowerPolynomial_eq_realified A j)
  rw [aeval_tracePowerPolynomial, map_mul, MvPolynomial.aeval_C,
    aeval_trace_polynomial_pow] at h
  unfold signedTracePower
  rw [h]
  rw [show ((-1 : ℝ) ^ j / 4) = (-1 : ℝ) ^ j * (1 / 4) by ring]
  simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one]
  ring

end
end QuaternionicSymmetry.RealifiedTracePolynomial
