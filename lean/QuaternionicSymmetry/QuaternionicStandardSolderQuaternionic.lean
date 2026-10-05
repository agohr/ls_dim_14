import QuaternionicSymmetry.QuaternionicStandardSolderOperator

/-! The off-diagonal solder operator is quaternion-linear. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderQuaternionic
open QuaternionicStandardSolderOperator QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardHilbertStructure QuaternionicUnitQuaternionTransport
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

theorem column_I (v : E) (q : ℍ) :
    column S v (leftLineStructure.I q) = S.I (column S v q) := by
  change S.action (basisI * q) v = S.I (S.action q v)
  rw [map_mul]
  change S.action basisI (S.action q v) = _
  simp [S.action_apply, basisI]

theorem column_J (v : E) (q : ℍ) :
    column S v (leftLineStructure.J q) = S.J (column S v q) := by
  change S.action (basisJ * q) v = S.J (S.action q v)
  rw [map_mul]
  change S.action basisJ (S.action q v) = _
  simp [S.action_apply, basisJ]

theorem column_adjoint_I (v w : E) :
    (column S v).adjoint (S.I w) = leftLineStructure.I ((column S v).adjoint w) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left, S.I_skew,
    leftLineStructure.I_skew, ContinuousLinearMap.adjoint_inner_left, column_I]

theorem column_adjoint_J (v w : E) :
    (column S v).adjoint (S.J w) = leftLineStructure.J ((column S v).adjoint w) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left, S.J_skew,
    leftLineStructure.J_skew, ContinuousLinearMap.adjoint_inner_left, column_J]

theorem solderOperator_I (v : E) (z : StandardSpace (E := E)) :
    solderOperator S v ((standardStructure S).I z) =
      (standardStructure S).I (solderOperator S v z) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · exact column_I S v z.snd
  · change -(column S v).adjoint (S.I z.fst) =
      leftLineStructure.I (-(column S v).adjoint z.fst)
    rw [column_adjoint_I, map_neg]

theorem solderOperator_J (v : E) (z : StandardSpace (E := E)) :
    solderOperator S v ((standardStructure S).J z) =
      (standardStructure S).J (solderOperator S v z) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · exact column_J S v z.snd
  · change -(column S v).adjoint (S.J z.fst) =
      leftLineStructure.J (-(column S v).adjoint z.fst)
    rw [column_adjoint_J, map_neg]

end
end QuaternionicSymmetry.QuaternionicStandardSolderQuaternionic
