import QuaternionicSymmetry.QuaternionicStandardSolderSquare
import QuaternionicSymmetry.QuaternionicProjectiveStandardLie
import QuaternionicSymmetry.QuaternionicLeftLineAction

/-! Explicit quaternion coordinates for the solder adjoint and its line
curvature block. These fix the factor two before scalar normalization. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderLine
open QuaternionicStandardSolderOperator QuaternionicStandardSolderSquare
open QuaternionicProjectiveStandardLie
open QuaternionicStandardSolderQuaternionic QuaternionicProjectiveStandardHilbertStructure
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance

theorem column_adjoint_coordinates (u v : E) :
    (column S u).adjoint v =
      (⟨inner ℝ u v, inner ℝ (S.I u) v, inner ℝ (S.J u) v,
        inner ℝ (S.K u) v⟩ : ℍ) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [column_apply, S.action_apply, Quaternion.inner_def,
    inner_add_right, real_inner_smul_right, real_inner_comm]

theorem lowerSquare_one (u v : E) :
    lowerSquare S u v 1 =
      (⟨0, -2 * inner ℝ (S.I u) v, -2 * inner ℝ (S.J u) v,
        -2 * inner ℝ (S.K u) v⟩ : ℍ) := by
  change (column S v).adjoint (S.action 1 u) -
      (column S u).adjoint (S.action 1 v) = _
  rw [map_one]
  change (column S v).adjoint u - (column S u).adjoint v = _
  rw [column_adjoint_coordinates, column_adjoint_coordinates]
  apply Quaternion.ext
  · simp [real_inner_comm]
  · change inner ℝ (S.I v) u - inner ℝ (S.I u) v = -2 * inner ℝ (S.I u) v
    rw [S.I_skew, real_inner_comm v (S.I u)]
    ring
  · change inner ℝ (S.J v) u - inner ℝ (S.J u) v = -2 * inner ℝ (S.J u) v
    rw [S.J_skew, real_inner_comm v (S.J u)]
    ring
  · change inner ℝ (S.K v) u - inner ℝ (S.K u) v = -2 * inner ℝ (S.K u) v
    rw [S.K_skew, real_inner_comm v (S.K u)]
    ring

theorem lowerSquare_apply (u v : E) (q : ℍ) :
    lowerSquare S u v q = q * lowerSquare S u v 1 := by
  apply QuaternionicLeftLineAction.apply_eq_mul_one (lowerSquare S u v).toLinearMap
  · intro w
    change (column S v).adjoint (column S u (leftLineStructure.I w)) -
        (column S u).adjoint (column S v (leftLineStructure.I w)) =
      leftLineStructure.I ((column S v).adjoint (column S u w) -
        (column S u).adjoint (column S v w))
    rw [column_I, column_I, column_adjoint_I, column_adjoint_I, map_sub]
  · intro w
    change (column S v).adjoint (column S u (leftLineStructure.J w)) -
        (column S u).adjoint (column S v (leftLineStructure.J w)) =
      leftLineStructure.J ((column S v).adjoint (column S u w) -
        (column S u).adjoint (column S v w))
    rw [column_J, column_J, column_adjoint_J, column_adjoint_J, map_sub]

end
end QuaternionicSymmetry.QuaternionicStandardSolderLine
