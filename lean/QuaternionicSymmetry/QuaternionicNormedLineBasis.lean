import QuaternionicSymmetry.QuaternionicLineMatrixCoordinates

/-! Real quaternion coordinate basis built from the normed-space linear
isometry, coherent with continuous endomorphism module instances. -/
namespace QuaternionicSymmetry.QuaternionicNormedLineBasis
open QuaternionicUniversalEvenTrace QuaternionicProjectiveStandardLie
  QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
open scoped Quaternion
noncomputable section

private def lineEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] ℍ :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.trans
    Quaternion.linearIsometryEquivTuple.symm.toLinearEquiv

def lineBasis : Module.Basis (Fin 4) ℝ ℍ :=
  (Pi.basisFun ℝ (Fin 4)).map lineEquiv

@[simp] theorem lineBasis_repr_zero (q : ℍ) : (lineBasis.repr q) 0 = q.re := by
  simp [lineBasis, lineEquiv, Quaternion.linearIsometryEquivTuple_apply]
@[simp] theorem lineBasis_repr_one (q : ℍ) : (lineBasis.repr q) 1 = q.imI := by
  simp [lineBasis, lineEquiv, Quaternion.linearIsometryEquivTuple_apply]
@[simp] theorem lineBasis_repr_two (q : ℍ) : (lineBasis.repr q) 2 = q.imJ := by
  simp [lineBasis, lineEquiv, Quaternion.linearIsometryEquivTuple_apply]
@[simp] theorem lineBasis_repr_three (q : ℍ) : (lineBasis.repr q) 3 = q.imK := by
  simp [lineBasis, lineEquiv, Quaternion.linearIsometryEquivTuple_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The concrete scalar-line matrix formula in a basis coherent with CLM
normed-space structures. -/
theorem scalarLineLie_matrix (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) :
    LinearMap.toMatrix lineBasis lineBasis (scalarLineLie S A).toLinearMap =
      lineMatrix (axialProjection (adjointRepresentation S A)) := by
  let a := axialProjection (adjointRepresentation S A)
  have hA : scalarLineLie S A =
      (ContinuousLinearMap.mul ℝ ℍ).flip (-(imaginary a)) := rfl
  rw [hA]
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (lineBasis.repr (lineBasis j * (-(imaginary a)))) i = lineMatrix a i j
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix, lineBasis, lineEquiv, imaginary_re, imaginary_imI,
      imaginary_imJ, imaginary_imK, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

end
end QuaternionicSymmetry.QuaternionicNormedLineBasis
