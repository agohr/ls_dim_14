import QuaternionicSymmetry.QuaternionicUniversalEvenTrace
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws

/-! The explicit universal rank-three matrix is the matrix of the actual
quaternionic adjoint representation in the named I,J,K basis. -/
namespace QuaternionicSymmetry.QuaternionicAdjointMatrixCoordinates
open QuaternionicUniversalEvenTrace
  QuaternionicLieAlgebraProjection
  ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem adjointRepresentation_synth_matrix (S : QuaternionicStructure E)
    (a : Fin 3 → ℝ) :
    (adjointRepresentation S (synth S a)).toLinearMap =
      Matrix.toLin' (adjointMatrix a) := by
  apply LinearMap.ext
  intro b
  ext i
  fin_cases i <;>
    simp [adjointRepresentation_synth, crossProduct,
      Matrix.toLin'_apply, Matrix.mulVec, adjointMatrix,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring_nf

end
end QuaternionicSymmetry.QuaternionicAdjointMatrixCoordinates
