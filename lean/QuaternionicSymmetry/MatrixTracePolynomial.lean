import QuaternionicSymmetry.ComplexPolynomialRealPart
import QuaternionicSymmetry.OrbitalConjugateSchur

/-! Polynomial trace invariants of finite real linear combinations of
complex matrices, with exact evaluation in complexified real algebras. -/

namespace QuaternionicSymmetry.MatrixTracePolynomial

open Matrix ComplexPolynomialRealPart CompactSymplecticTraceInvariants OrbitalConjugateSchur
open scoped TensorProduct

noncomputable section

variable {β κ : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]

def matrixPolynomial (A : β → Matrix κ κ ℂ) : Matrix κ κ (MvPolynomial β ℂ) :=
  fun i j => ∑ b, MvPolynomial.C (A b i j) * MvPolynomial.X b

def matrixCombination (A : β → Matrix κ κ ℂ) (x : β → ℝ) : Matrix κ κ ℂ :=
  ∑ b, (x b : ℂ) • A b

theorem eval_matrixPolynomial (A : β → Matrix κ κ ℂ) (x : β → ℝ) :
    (MvPolynomial.eval (fun b => (x b : ℂ))).mapMatrix (matrixPolynomial A) =
      matrixCombination A x := by
  ext i j
  simp [matrixPolynomial, matrixCombination, Matrix.sum_apply, mul_comm]

def tracePowerPolynomial (A : β → Matrix κ κ ℂ) (r : ℕ) : MvPolynomial β ℝ :=
  MvPolynomial.C (1 / 2 : ℝ) *
    realCoefficients (Matrix.trace (matrixPolynomial A ^ (2 * r)))

theorem eval_tracePowerPolynomial (A : β → Matrix κ κ ℂ) (r : ℕ) (x : β → ℝ) :
    (tracePowerPolynomial A r).eval x = evenTracePower (matrixCombination A x) r := by
  rw [tracePowerPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_realCoefficients]
  have ht : (MvPolynomial.eval (fun b => (x b : ℂ)))
      (Matrix.trace (matrixPolynomial A ^ (2 * r))) =
      Matrix.trace (matrixCombination A x ^ (2 * r)) := by
    rw [AddMonoidHom.map_trace]
    change Matrix.trace ((MvPolynomial.eval (fun b => (x b : ℂ))).mapMatrix
      (matrixPolynomial A ^ (2 * r))) = _
    rw [map_pow, eval_matrixPolynomial]
  rw [ht]
  unfold evenTracePower
  ring

variable {S : Type*} [CommRing S] [Algebra ℝ S]

def complexifiedMatrix (A : β → Matrix κ κ ℂ) (η : β → S) :
    Matrix κ κ (ℂ ⊗[ℝ] S) := fun i j => ∑ b, A b i j ⊗ₜ[ℝ] η b

/-- Power sums with the sign from the anti-Hermitian curvature convention. -/
def signedTracePower (X : Matrix κ κ (ℂ ⊗[ℝ] S)) (r : ℕ) : S :=
  (-1 : S) ^ r * ((1 / 2 : ℝ) •
    Complexification.realPart (Matrix.trace (X ^ (2 * r))))

/-- The signed power sums are exactly half the real trace of powers of
`Y = -X²`, the convention in the paper. -/
theorem signedTracePower_eq_square (X : Matrix κ κ (ℂ ⊗[ℝ] S)) (r : ℕ) :
    signedTracePower X r = (1 / 2 : ℝ) •
      Complexification.realPart (Matrix.trace ((-X ^ 2) ^ r)) := by
  have hpow : (-X ^ 2) ^ r = (-1 : ℝ) ^ r • X ^ (2 * r) := by
    rw [← neg_one_smul ℝ (X ^ 2), smul_pow, ← pow_mul]
  rw [hpow, Matrix.trace_smul, map_smul]
  simp only [signedTracePower, Algebra.smul_def, map_pow, map_neg, map_one]
  ring

theorem complexifiedEvaluation_matrixPolynomial (A : β → Matrix κ κ ℂ) (η : β → S) :
    (complexifiedEvaluation η).mapMatrix (matrixPolynomial A) =
      complexifiedMatrix A η := by
  ext i j
  simp [matrixPolynomial, complexifiedMatrix, complexifiedEvaluation,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Polynomial substitution equals the actual real part of the matrix trace
in the complexified coefficient algebra. No reducedness or norm is needed. -/
theorem aeval_tracePowerPolynomial (A : β → Matrix κ κ ℂ) (r : ℕ) (η : β → S) :
    MvPolynomial.aeval η (tracePowerPolynomial A r) =
      (1 / 2 : ℝ) • Complexification.realPart
        (Matrix.trace (complexifiedMatrix A η ^ (2 * r))) := by
  rw [tracePowerPolynomial, map_mul, MvPolynomial.aeval_C, aeval_realCoefficients]
  have ht : complexifiedEvaluation η (Matrix.trace (matrixPolynomial A ^ (2 * r))) =
      Matrix.trace (complexifiedMatrix A η ^ (2 * r)) := by
    rw [AddMonoidHom.map_trace]
    change Matrix.trace ((complexifiedEvaluation η).mapMatrix
      (matrixPolynomial A ^ (2 * r))) = _
    rw [map_pow, complexifiedEvaluation_matrixPolynomial]
  rw [ht, Algebra.smul_def]

def schurPolynomial (A : β → Matrix κ κ ℂ) (lam : List ℕ) : MvPolynomial β ℝ :=
  MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
    (FiniteTypeCSchurSix.schur lam)

theorem eval_schurPolynomial (A : β → Matrix κ κ ℂ) (lam : List ℕ) (x : β → ℝ) :
    (schurPolynomial A lam).eval x = matrixSchurValue (matrixCombination A x) lam := by
  change ((MvPolynomial.aeval x).restrictScalars ℚ)
    (MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
      (FiniteTypeCSchurSix.schur lam)) = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [matrixSchurValue]
  exact congrArg (fun f : Fin 6 → ℝ => MvPolynomial.aeval f
    (FiniteTypeCSchurSix.schur lam))
    (funext (fun i => eval_tracePowerPolynomial A (i.val + 1) x))

end
end QuaternionicSymmetry.MatrixTracePolynomial
