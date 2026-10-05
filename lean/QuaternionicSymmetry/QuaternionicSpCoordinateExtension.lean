import QuaternionicSymmetry.HomogeneousMatrixCombinations
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A fixed continuous extension of each centralizer-basis coordinate
to the ambient real endomorphism space. On symplectic operators it is
the genuine basis coordinate. -/
namespace QuaternionicSymmetry.QuaternionicSpCoordinateExtension
open QuaternionicCurvatureFiniteExpansion Module
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S : QuaternionicStructure E)

private def coordinateLinear (a : Index S) :
    (E →L[ℝ] E) →ₗ[ℝ] ℝ :=
  Classical.choose (LinearMap.exists_extend ((operatorBasis S).coord a))

def coordinate (a : Index S) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (coordinateLinear S a).toContinuousLinearMap

omit [Nontrivial E] in
theorem coordinate_apply_mem (a : Index S) (T : operatorSpace S) :
    coordinate S a T.val = (operatorBasis S).repr T a := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend ((operatorBasis S).coord a))
  exact congrArg (fun f : operatorSpace S →ₗ[ℝ] ℝ => f T) h

omit [Nontrivial E] in
theorem expansion_mem (T : operatorSpace S) :
    ∑ a : Index S, coordinate S a T.val • (operatorBasis S a).val = T.val := by
  have h := (operatorBasis S).sum_repr T
  simpa only [Submodule.coe_sum, Submodule.coe_smul,
    ← coordinate_apply_mem S] using congrArg (fun U : operatorSpace S => U.val) h

end
end QuaternionicSymmetry.QuaternionicSpCoordinateExtension
