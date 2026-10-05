import QuaternionicSymmetry.QuaternionicStandardSolderLine

/-! The compact real model of the `R_E` term of the quaternionic curvature
decomposition is the sum of four elementary skew operators. Its exact
normalization is obtained from the adjoint of the genuine quaternionic
column in the standard representation. -/
namespace QuaternionicSymmetry.QuaternionicKSWUpperModel
open QuaternionicStandardSolderOperator
open QuaternionicStandardSolderSquare
open QuaternionicStandardSolderLine
open QuaternionicStandardSolderQuaternionic
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

/-- The four elementary wedges appearing in KSW Appendix B.28, in the
real quaternionic model with the solder-commutator sign convention. -/
def compactWedgeSum (u v w : E) : E :=
  (inner ℝ u w • v - inner ℝ v w • u) +
  (inner ℝ (S.I u) w • S.I v - inner ℝ (S.I v) w • S.I u) +
  (inner ℝ (S.J u) w • S.J v - inner ℝ (S.J v) w • S.J u) +
  (inner ℝ (S.K u) w • S.K v - inner ℝ (S.K v) w • S.K u)

theorem upperSquare_apply_compactWedgeSum (u v w : E) :
    upperSquare S u v w = compactWedgeSum S u v w := by
  rw [upperSquare]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [column_adjoint_coordinates, column_adjoint_coordinates]
  simp only [column_apply, S.action_apply]
  simp [compactWedgeSum]
  abel

/-- The real action of the source's `R_E` term in Eq. (3.8). The factor
`1/2` accounts for the doubling when the wedge-valued form in B.28 is
evaluated on two tangent vectors. -/
def sourceRE (u v w : E) : E :=
  (1 / 2 : ℝ) • compactWedgeSum S u v w

/-- The endomorphism realization of the same source tensor. -/
def sourceREOperator (u v : E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • upperSquare S u v

theorem sourceREOperator_apply (u v w : E) :
    sourceREOperator S u v w = sourceRE S u v w := by
  simp [sourceREOperator, sourceRE, upperSquare_apply_compactWedgeSum]

theorem upperSquare_apply_eq_twice_sourceRE (u v w : E) :
    upperSquare S u v w = (2 : ℝ) • sourceRE S u v w := by
  rw [upperSquare_apply_compactWedgeSum]
  simp [sourceRE, smul_smul]

theorem upperSquare_commutes_I (u v w : E) :
    upperSquare S u v (S.I w) = S.I (upperSquare S u v w) := by
  change column S v ((column S u).adjoint (S.I w)) -
      column S u ((column S v).adjoint (S.I w)) =
    S.I (column S v ((column S u).adjoint w) -
      column S u ((column S v).adjoint w))
  rw [column_adjoint_I, column_adjoint_I, column_I, column_I, map_sub]

theorem upperSquare_commutes_J (u v w : E) :
    upperSquare S u v (S.J w) = S.J (upperSquare S u v w) := by
  change column S v ((column S u).adjoint (S.J w)) -
      column S u ((column S v).adjoint (S.J w)) =
    S.J (column S v ((column S u).adjoint w) -
      column S u ((column S v).adjoint w))
  rw [column_adjoint_J, column_adjoint_J, column_J, column_J, map_sub]

omit [FiniteDimensional ℝ E] in
private theorem transformed_wedge_pair (T : E ≃ₗᵢ[ℝ] E)
    (hsk : ∀ a b : E, inner ℝ (T a) b = -inner ℝ a (T b))
    (u v w z : E) :
    inner ℝ (inner ℝ (T u) w • T v - inner ℝ (T v) w • T u) z =
      inner ℝ (inner ℝ (T w) u • T z - inner ℝ (T z) u • T w) v := by
  have hs (a b : E) : inner ℝ (T a) b = -inner ℝ (T b) a := by
    rw [hsk a b, real_inner_comm a]
  simp only [inner_sub_left, real_inner_smul_left]
  rw [hs u w, hs v z, hs v w, hs u z]
  ring

omit [FiniteDimensional ℝ E] in
private theorem plain_wedge_pair (u v w z : E) :
    inner ℝ (inner ℝ u w • v - inner ℝ v w • u) z =
      inner ℝ (inner ℝ w u • z - inner ℝ z u • w) v := by
  simp only [inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm u w, real_inner_comm v z,
    real_inner_comm v w, real_inner_comm u z]
  ring

omit [FiniteDimensional ℝ E] in
theorem compactWedgeSum_pair_symmetry (u v w z : E) :
    inner ℝ (compactWedgeSum S u v w) z =
      inner ℝ (compactWedgeSum S w z u) v := by
  simp only [compactWedgeSum, inner_add_left]
  rw [plain_wedge_pair, transformed_wedge_pair S.I S.I_skew,
    transformed_wedge_pair S.J S.J_skew,
    transformed_wedge_pair S.K S.K_skew]

omit [FiniteDimensional ℝ E] in
/-- The source `R_E` model is symmetric under interchange of its two
argument pairs. -/
theorem sourceRE_pair_symmetry (u v w z : E) :
    inner ℝ (sourceRE S u v w) z = inner ℝ (sourceRE S w z u) v := by
  simp only [sourceRE, real_inner_smul_left]
  rw [compactWedgeSum_pair_symmetry]

end
end QuaternionicSymmetry.QuaternionicKSWUpperModel
