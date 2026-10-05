import QuaternionicSymmetry.QuaternionicUniversalEvenTrace
import QuaternionicSymmetry.QuaternionicProjectiveStandardLie

/-! The universal four-by-four line matrix is the real matrix of actual
right multiplication by the negative imaginary quaternion. -/
namespace QuaternionicSymmetry.QuaternionicLineMatrixCoordinates
open QuaternionicUniversalEvenTrace QuaternionicProjectiveStandardLie
  QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem scalarLineLie_matrix (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) :
    LinearMap.toMatrix
      (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))
      (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))
      (scalarLineLie S A).toLinearMap =
    lineMatrix (axialProjection (adjointRepresentation S A)) := by
  let a := axialProjection (adjointRepresentation S A)
  have hA : scalarLineLie S A =
      (ContinuousLinearMap.mul ℝ ℍ).flip (-(imaginary a)) := rfl
  rw [hA]
  ext i j
  rw [LinearMap.toMatrix_apply]
  change ((QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)).repr
    ((show ℍ from (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)) j) *
      (-(imaginary a)))) i = lineMatrix a i j
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix, imaginary_re, imaginary_imI, imaginary_imJ,
      imaginary_imK,
      QuaternionAlgebra.basisOneIJK,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

end
end QuaternionicSymmetry.QuaternionicLineMatrixCoordinates
