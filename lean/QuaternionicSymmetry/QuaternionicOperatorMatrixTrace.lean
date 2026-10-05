import QuaternionicSymmetry.QuaternionicOperatorMatrixLinear
import Mathlib.LinearAlgebra.Trace

/-! Exact real-versus-complex trace normalization in the fixed matrix
coordinates, independent of the choice of quaternionic basis. -/
namespace QuaternionicSymmetry.QuaternionicOperatorMatrixTrace
open QuaternionicOperatorMatrix QuaternionicMatrixCoordinates QuaternionicMatrixModel
open scoped Matrix
noncomputable section

private theorem leftMulMatrix_trace (z : ℂ) :
    (Algebra.leftMulMatrix Complex.basisOneI z).trace = 2 * z.re := by
  rw [Matrix.trace, Fin.sum_univ_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI_repr,
    Complex.coe_basisOneI, Complex.mul_re, Complex.mul_im]
  ring

theorem trace_restrictScalars {W : Type*} [AddCommGroup W]
    [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    [FiniteDimensional ℝ W] [FiniteDimensional ℂ W] (A : W →ₗ[ℂ] W) :
    LinearMap.trace ℝ W (A.restrictScalars ℝ) =
      2 * (LinearMap.trace ℂ W A).re := by
  let b := Module.Free.chooseBasis ℂ W
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' b),
    LinearMap.restrictScalars_toMatrix Complex.basisOneI b A,
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.comp_apply, Matrix.map_apply]
  change ∑ x, (Algebra.leftMulMatrix Complex.basisOneI
      ((LinearMap.toMatrix b b) A x x)).trace = _
  simp_rw [leftMulMatrix_trace]
  rw [← Finset.mul_sum]
  congr 1
  exact (Complex.re_sum _ _).symm

theorem realMatrixAction_trace {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    LinearMap.trace ℝ (V n) (realMatrixAction A) = 2 * A.trace.re := by
  rw [realMatrixAction, trace_restrictScalars]
  congr 2
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun _ ℂ).toBasis,
    LinearMap.toMatrix_toLin]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

theorem operatorMatrix_trace (A : E →ₗ[ℝ] E)
    (hI : ∀ v, A (S.I v) = S.I (A v)) :
    LinearMap.trace ℝ E A = 2 * (operatorMatrix S A hI).trace.re := by
  have h := realMatrixAction_trace (operatorMatrix S A hI)
  have he : realMatrixAction (operatorMatrix S A hI) = modelEnd S A := by
    apply LinearMap.ext
    intro v
    exact matrixEnd_action _ _ v
  rw [he, modelEnd, LinearMap.trace_conj'] at h
  exact h

end
end QuaternionicSymmetry.QuaternionicOperatorMatrixTrace
