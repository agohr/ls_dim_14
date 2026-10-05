import QuaternionicSymmetry.MatrixTraceReality
import QuaternionicSymmetry.QuaternionicAhatPositivity

/-! Identification of the existing full-trace moment variables with the
half-trace orbital variables, using the same actual complexified matrix. -/
namespace QuaternionicSymmetry.QuaternionicTraceConventionBridge

open QuaternionicFundamental QuaternionicTracePositivity MatrixTracePolynomial
open scoped TensorProduct
noncomputable section

variable {κ β V : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [Fintype κ] [DecidableEq κ] in
theorem weightedMatrix_eq_complexifiedMatrix
    (B : β → Matrix κ κ ℂ) (η : β → E V) :
    MatrixValuedForms.weightedMatrix B (fun b => embed (V := V) (η b)) =
      complexifiedMatrix B η := by
  ext i j
  simp [MatrixValuedForms.weightedMatrix, MatrixValuedForms.mapMatrix,
    complexifiedMatrix, embed, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem tracePower_eq_twice_halfTrace
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (j : ℕ) :
    QuaternionicAhatPositivity.tracePower B η j =
      2 * embed (V := V) (signedTracePower (complexifiedMatrix B η) j) := by
  unfold QuaternionicAhatPositivity.tracePower QuaternionicGaussianTraceMoments.curvatureSquare
  rw [weightedMatrix_eq_complexifiedMatrix]
  rw [show embed (V := V) (signedTracePower (complexifiedMatrix B η) j) =
      (1 / 2 : ℝ) • Matrix.trace ((-(complexifiedMatrix B η)^2)^j) from
    MatrixTraceReality.includeRight_signedTracePower_eq_half_trace_square
      B (fun b => (hB b).eq) η j]
  have hscale (t : CE V) : (2 : CE V) * ((1 / 2 : ℝ) • t) = t := by
    calc
      _ = (1 / 2 : ℝ) • t + (1 / 2 : ℝ) • t := two_mul ((1 / 2 : ℝ) • t)
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • t := (add_smul (1 / 2 : ℝ) (1 / 2 : ℝ) t).symm
      _ = t := by norm_num
  exact (hscale _).symm

end
end QuaternionicSymmetry.QuaternionicTraceConventionBridge
