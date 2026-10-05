import QuaternionicSymmetry.QuaternionicStandardSolderQuaternionic
import QuaternionicSymmetry.OperatorBlockDerivative

/-! The two diagonal blocks of the solder commutator, with its signs fixed
by the genuine Hilbert adjoint in the off-diagonal operator. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderSquare
open QuaternionicStandardSolderOperator QuaternionicProjectiveStandardL2
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance

def upperSquare (u v : E) : E →L[ℝ] E :=
  (column S v).comp (column S u).adjoint - (column S u).comp (column S v).adjoint

def lowerSquare (u v : E) : ℍ →L[ℝ] ℍ :=
  (column S v).adjoint.comp (column S u) - (column S u).adjoint.comp (column S v)

theorem solder_commutator (u v : E) :
    solderOperator S u * solderOperator S v - solderOperator S v * solderOperator S u =
      OperatorBlockDerivative.blockOperator (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
        (upperSquare S u v) (lowerSquare S u v) := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change column S u (-(column S v).adjoint z.fst) -
        column S v (-(column S u).adjoint z.fst) =
      column S v ((column S u).adjoint z.fst) - column S u ((column S v).adjoint z.fst)
    simp only [map_neg]
    abel
  · change -(column S u).adjoint (column S v z.snd) -
        -(column S v).adjoint (column S u z.snd) =
      (column S v).adjoint (column S u z.snd) - (column S u).adjoint (column S v z.snd)
    abel

end
end QuaternionicSymmetry.QuaternionicStandardSolderSquare
