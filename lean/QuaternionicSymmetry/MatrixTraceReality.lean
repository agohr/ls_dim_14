import QuaternionicSymmetry.MatrixTracePolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! Reality of trace power sums after substitution into any commutative real algebra. -/

namespace QuaternionicSymmetry.MatrixTraceReality

open Matrix ComplexPolynomialRealPart MatrixTracePolynomial
open scoped TensorProduct

noncomputable section

variable {β κ : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]

private theorem trace_matrixCombination_real
    (A : β → Matrix κ κ ℂ) (hA : ∀ b, (A b)ᴴ = A b)
    (r : ℕ) (x : β → ℝ) :
    (Matrix.trace (matrixCombination A x ^ r)).im = 0 := by
  have hH : (matrixCombination A x)ᴴ = matrixCombination A x := by
    simp [matrixCombination, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hA]
  have ht : star (Matrix.trace (matrixCombination A x ^ r)) =
      Matrix.trace (matrixCombination A x ^ r) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_pow, hH]
  exact Complex.conj_eq_iff_im.mp ht

private theorem tracePolynomial_eq_map_realCoefficients
    (A : β → Matrix κ κ ℂ) (hA : ∀ b, (A b)ᴴ = A b) (r : ℕ) :
    Matrix.trace (matrixPolynomial A ^ r) =
      MvPolynomial.map (algebraMap ℝ ℂ)
        (realCoefficients (Matrix.trace (matrixPolynomial A ^ r))) := by
  let s : β → Set ℂ := fun _ => Set.range (fun t : ℝ => (t : ℂ))
  apply MvPolynomial.funext_set s (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose y hy using fun b => hx b (Set.mem_univ b)
  have hxy : x = fun b => (y b : ℂ) := funext (fun b => (hy b).symm)
  subst x
  rw [MvPolynomial.eval_map]
  have hcomp : MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun b => (y b : ℂ))
      (realCoefficients (Matrix.trace (matrixPolynomial A ^ r))) =
      ((MvPolynomial.eval y
        (realCoefficients (Matrix.trace (matrixPolynomial A ^ r))) : ℝ) : ℂ) := by
    simpa only [Function.comp_def] using
      (MvPolynomial.eval₂_comp (algebraMap ℝ ℂ) y
        (realCoefficients (Matrix.trace (matrixPolynomial A ^ r)))).symm
  rw [hcomp]
  have heval : (MvPolynomial.eval (fun b => (y b : ℂ)))
      (Matrix.trace (matrixPolynomial A ^ r)) =
      Matrix.trace (matrixCombination A y ^ r) := by
    rw [AddMonoidHom.map_trace]
    change Matrix.trace ((MvPolynomial.eval (fun b => (y b : ℂ))).mapMatrix
      (matrixPolynomial A ^ r)) = _
    rw [map_pow, eval_matrixPolynomial]
  rw [heval, eval_realCoefficients]
  exact Complex.ext (by simp [heval])
    (by simp [heval, trace_matrixCombination_real A hA r y])

variable {S : Type*} [CommRing S] [Algebra ℝ S]

omit [Fintype β] in
private theorem complexifiedEvaluation_map_real (η : β → S)
    (q : MvPolynomial β ℝ) :
    complexifiedEvaluation η (MvPolynomial.map (algebraMap ℝ ℂ) q) =
      Algebra.TensorProduct.includeRight (MvPolynomial.aeval η q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial d a =>
    simp only [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial,
      complexifiedEvaluation, MvPolynomial.eval₂Hom_monomial]
    simp only [Algebra.TensorProduct.includeRight_apply, Finsupp.prod]
    have hc : (↑a : ℂ) ⊗ₜ[ℝ] (1 : S) =
        (1 : ℂ) ⊗ₜ[ℝ] ((algebraMap ℝ S) a) := by
      simpa [Algebra.smul_def] using
        (TensorProduct.smul_tmul (R := ℝ) a (1 : ℂ) (1 : S))
    change ((a : ℂ) ⊗ₜ[ℝ] (1 : S)) *
      (∏ x ∈ d.support, (1 : ℂ) ⊗ₜ[ℝ] η x ^ d x) = _
    rw [hc]
    simp only [← Algebra.TensorProduct.includeRight_apply, map_mul, map_prod, map_pow]
  | add p q hp hq =>
    simpa only [map_add] using congrArg₂ (· + ·) hp hq

/-- The trace of every power of a matrix with Hermitian numerical coefficients
has real coefficients, even after substitution into a nonreduced real algebra. -/
theorem trace_complexifiedMatrix_eq_includeRight (A : β → Matrix κ κ ℂ)
    (hA : ∀ b, (A b)ᴴ = A b) (η : β → S) (r : ℕ) :
    Matrix.trace (complexifiedMatrix A η ^ r) =
      Algebra.TensorProduct.includeRight
        (Complexification.realPart (Matrix.trace (complexifiedMatrix A η ^ r))) := by
  have ht : complexifiedEvaluation η (Matrix.trace (matrixPolynomial A ^ r)) =
      Matrix.trace (complexifiedMatrix A η ^ r) := by
    rw [AddMonoidHom.map_trace]
    change Matrix.trace ((complexifiedEvaluation η).mapMatrix
      (matrixPolynomial A ^ r)) = _
    rw [map_pow, complexifiedEvaluation_matrixPolynomial]
  rw [← ht, tracePolynomial_eq_map_realCoefficients A hA r,
    complexifiedEvaluation_map_real]
  simp

/-- Literal half trace of `Y = -X²` equals the real signed power sum used by
the finite orbital theorem; the equality is inside the complexified algebra. -/
theorem includeRight_signedTracePower_eq_half_trace_square
    (A : β → Matrix κ κ ℂ) (hA : ∀ b, (A b)ᴴ = A b)
    (η : β → S) (r : ℕ) :
    Algebra.TensorProduct.includeRight (signedTracePower (complexifiedMatrix A η) r) =
      (1 / 2 : ℝ) • Matrix.trace ((-(complexifiedMatrix A η) ^ 2) ^ r) := by
  rw [signedTracePower_eq_square]
  have hpow : (-(complexifiedMatrix A η) ^ 2) ^ r =
      (-1 : ℝ) ^ r • (complexifiedMatrix A η) ^ (2 * r) := by
    rw [← neg_one_smul ℝ ((complexifiedMatrix A η) ^ 2), smul_pow, ← pow_mul]
  rw [hpow, Matrix.trace_smul, map_smul]
  rw [trace_complexifiedMatrix_eq_includeRight A hA η (2 * r)]
  simp only [map_smul, Complexification.realPart_includeRight]

end
end QuaternionicSymmetry.MatrixTraceReality
