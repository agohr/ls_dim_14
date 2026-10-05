import QuaternionicSymmetry.QuaternionicManifoldSmoothProductLifts
import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure

/-! The off-diagonal solder operator on the standard quaternionic Hilbert
space, with its genuine adjoint block and metric skewness. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderOperator
open QuaternionicManifoldSmoothProductLifts QuaternionicProjectiveStandardL2
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance

def column : E →L[ℝ] (ℍ →L[ℝ] E) :=
  (scalarActionLinear S).toContinuousLinearMap.flip

@[simp] theorem column_apply (v : E) (q : ℍ) :
    column S v q = S.action q v := rfl

private def coordinates : StandardSpace (E := E) ≃L[ℝ] E × ℍ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ

def offDiagonal (v : E) : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) :=
  (coordinates (E := E)).symm.toContinuousLinearMap.comp
    ((((column S v).comp (ContinuousLinearMap.snd ℝ E ℍ)).prod
      ((-(column S v).adjoint).comp (ContinuousLinearMap.fst ℝ E ℍ))).comp
        (coordinates (E := E)).toContinuousLinearMap)

theorem offDiagonal_blocks (v : E) (z : StandardSpace (E := E)) :
    (coordinates (E := E)) (offDiagonal S v z) =
      (column S v z.snd, -(column S v).adjoint z.fst) := rfl

def solderOperator : E →L[ℝ]
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  LinearMap.toContinuousLinearMap {
    toFun := offDiagonal S
    map_add' := by
      intro u v
      apply ContinuousLinearMap.ext
      intro z
      apply (coordinates (E := E)).injective
      simp only [map_add, offDiagonal_blocks, ContinuousLinearMap.add_apply]
      simp [add_comm]
    map_smul' := by
      intro r v
      apply ContinuousLinearMap.ext
      intro z
      apply (coordinates (E := E)).injective
      simp only [map_smul, offDiagonal_blocks, ContinuousLinearMap.smul_apply]
      simp
  }

theorem solderOperator_apply (v : E) : solderOperator S v = offDiagonal S v := rfl

theorem solderOperator_skew (v : E) (z w : StandardSpace (E := E)) :
    inner ℝ (solderOperator S v z) w + inner ℝ z (solderOperator S v w) = 0 := by
  change (inner ℝ (column S v z.snd) w.fst +
      inner ℝ (-(column S v).adjoint z.fst) w.snd) +
    (inner ℝ z.fst (column S v w.snd) +
      inner ℝ z.snd (-(column S v).adjoint w.fst)) = 0
  rw [inner_neg_left, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

end
end QuaternionicSymmetry.QuaternionicStandardSolderOperator
