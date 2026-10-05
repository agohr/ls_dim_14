import QuaternionicSymmetry.MatrixTracePolynomial

/-! Real scaling of the matrix coefficients gives the expected even weights
in every signed trace, over arbitrary real commutative coefficient algebras. -/
namespace QuaternionicSymmetry.MatrixTraceScaling
open MatrixTracePolynomial
open scoped TensorProduct
noncomputable section
variable {β κ R : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]
  [CommRing R] [Algebra ℝ R]

omit [Fintype κ] [DecidableEq κ] in
theorem complexifiedMatrix_smul (B : β → Matrix κ κ ℂ) (η : β → R) (r : ℝ) :
    complexifiedMatrix (fun b => r • B b) η = r • complexifiedMatrix B η := by
  ext i j
  simp [complexifiedMatrix, TensorProduct.smul_tmul', Finset.smul_sum]

theorem signedTracePower_smul (X : Matrix κ κ (ℂ ⊗[ℝ] R)) (r : ℝ) (j : ℕ) :
    signedTracePower (r • X) j = r ^ (2 * j) • signedTracePower X j := by
  simp only [signedTracePower, smul_pow, Matrix.trace_smul, map_smul,
    smul_comm (1 / 2 : ℝ), mul_smul_comm]

theorem signedTrace_coefficients_smul (B : β → Matrix κ κ ℂ) (η : β → R)
    (r : ℝ) (j : ℕ) :
    signedTracePower (complexifiedMatrix (fun b => r • B b) η) j =
      r ^ (2 * j) • signedTracePower (complexifiedMatrix B η) j := by
  rw [complexifiedMatrix_smul, signedTracePower_smul]

end
end QuaternionicSymmetry.MatrixTraceScaling
