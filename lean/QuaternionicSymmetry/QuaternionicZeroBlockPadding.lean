import QuaternionicSymmetry.QuaternionicTraceConventionBridge
import QuaternionicSymmetry.PrintedProjectionCubicPositivity
import Mathlib.Data.Matrix.Block

/-! Adding the zero H block changes the matrix rank by two and leaves every
positive trace power unchanged, as required by the projection certificates. -/
namespace QuaternionicSymmetry.QuaternionicZeroBlockPadding

open Matrix MatrixTracePolynomial QuaternionicFundamental QuaternionicTracePositivity
  QuaternionicTraceConventionBridge PrintedProjectionCubicPositivity

noncomputable section
variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [CommRing S]

def padTwo (B : Matrix κ κ S) : Matrix (κ ⊕ Fin 2) (κ ⊕ Fin 2) S :=
  Matrix.fromBlocks B 0 0 0

omit [Fintype κ] [DecidableEq κ] in
theorem padTwo_neg (B : Matrix κ κ S) : padTwo (-B) = -padTwo B := by
  ext (i | i) (j | j) <;> simp [padTwo]

theorem padTwo_pow (B : Matrix κ κ S) (j : ℕ) (hj : 0 < j) :
    padTwo B ^ j = padTwo (B ^ j) := by
  rw [padTwo, Matrix.fromBlocks_diagonal_pow]
  simp [padTwo, ne_of_gt hj]

omit [DecidableEq κ] in
theorem trace_padTwo (B : Matrix κ κ S) : Matrix.trace (padTwo B) = Matrix.trace B := by
  simp [Matrix.trace, padTwo, Fintype.sum_sum_type]

omit [Fintype κ] [DecidableEq κ] in
theorem padTwo_isHermitian (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    (padTwo B).IsHermitian := by
  change (padTwo B)ᴴ = padTwo B
  ext (i | i) (j | j)
  · exact congrArg (fun A : Matrix κ κ ℂ => A i j) hB.eq
  all_goals simp [padTwo, Matrix.conjTranspose_apply]

variable {β V : Type*} [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [Fintype κ] [DecidableEq κ] in
theorem complexifiedMatrix_padTwo (B : β → Matrix κ κ ℂ) (η : β → E V) :
    complexifiedMatrix (fun b => padTwo (B b)) η = padTwo (complexifiedMatrix B η) := by
  ext (i | i) (j | j) <;> simp [complexifiedMatrix, padTwo]

theorem tracePower_padTwo (B : β → Matrix κ κ ℂ) (η : β → E V)
    (j : ℕ) (hj : 0 < j) :
    QuaternionicAhatPositivity.tracePower (fun b => padTwo (B b)) η j =
      QuaternionicAhatPositivity.tracePower B η j := by
  unfold QuaternionicAhatPositivity.tracePower QuaternionicGaussianTraceMoments.curvatureSquare
  rw [weightedMatrix_eq_complexifiedMatrix, weightedMatrix_eq_complexifiedMatrix,
    complexifiedMatrix_padTwo, padTwo_pow _ 2 (by decide), ← padTwo_neg,
    padTwo_pow _ j hj, trace_padTwo]

theorem signedTracePower_padTwo (B : β → Matrix κ κ ℂ) (η : β → E V)
    (j : ℕ) (hj : 0 < j) :
    signedTracePower (complexifiedMatrix (fun b => padTwo (B b)) η) j =
      signedTracePower (complexifiedMatrix B η) j := by
  unfold signedTracePower
  rw [complexifiedMatrix_padTwo, padTwo_pow _ (2*j) (by omega), trace_padTwo]

theorem densityValues_padTwo {ι : Type*} [Fintype ι]
    (Q : QuaternionicStructure V) (c : Module.Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (η : β → E V) :
    densityValues Q c (fun b => padTwo (B b)) η = densityValues Q c B η := by
  unfold densityValues
  rw [signedTracePower_padTwo B η 1 (by decide), signedTracePower_padTwo B η 2 (by decide),
    signedTracePower_padTwo B η 3 (by decide), signedTracePower_padTwo B η 4 (by decide),
    signedTracePower_padTwo B η 5 (by decide)]

end
end QuaternionicSymmetry.QuaternionicZeroBlockPadding
