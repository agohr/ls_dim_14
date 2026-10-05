import QuaternionicSymmetry.QuaternionicKSWUpperModel
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Ricci contraction of the explicit scalar quaternionic curvature model. -/
namespace QuaternionicSymmetry.QuaternionicKSWModelRicci
open QuaternionicKSWUpperModel
open QuaternionicStandardSolderSquare
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)

omit [Nontrivial E] in
theorem basis_inner_sum (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (stdOrthonormalBasis ℝ E a) v *
        inner ℝ w (stdOrthonormalBasis ℝ E a)) = inner ℝ w v := by
  let b := stdOrthonormalBasis ℝ E
  have h := congrArg (fun x : E => inner ℝ w x) (b.sum_repr' v)
  simpa only [inner_sum, real_inner_smul_right, mul_comm] using h

omit [Nontrivial E] in
theorem basis_skew_sum (T : E ≃ₗᵢ[ℝ] E)
    (hsk : ∀ a b : E, inner ℝ (T a) b = -inner ℝ a (T b))
    (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (T (stdOrthonormalBasis ℝ E a)) v *
        inner ℝ (T w) (stdOrthonormalBasis ℝ E a)) =
      -inner ℝ w v := by
  calc
    _ = ∑ a : Fin (Module.finrank ℝ E),
      (-inner ℝ (stdOrthonormalBasis ℝ E a) (T v)) *
        inner ℝ (T w) (stdOrthonormalBasis ℝ E a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hsk]
    _ = -(∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (stdOrthonormalBasis ℝ E a) (T v) *
        inner ℝ (T w) (stdOrthonormalBasis ℝ E a)) := by
          simp only [neg_mul, Finset.sum_neg_distrib]
    _ = -inner ℝ (T w) (T v) := by rw [basis_inner_sum]
    _ = -inner ℝ w v := by rw [T.inner_map_map]

omit [Nontrivial E] in
theorem basis_self_sum :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (stdOrthonormalBasis ℝ E a) (stdOrthonormalBasis ℝ E a)) =
      (Module.finrank ℝ E : ℝ) := by
  simp

omit [Nontrivial E] in
theorem transformed_wedge_ricci (T : E ≃ₗᵢ[ℝ] E)
    (hsk : ∀ a b : E, inner ℝ (T a) b = -inner ℝ a (T b))
    (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ
        (inner ℝ (T (stdOrthonormalBasis ℝ E a)) w • T v -
          inner ℝ (T v) w • T (stdOrthonormalBasis ℝ E a))
        (stdOrthonormalBasis ℝ E a)) = -inner ℝ v w := by
  have hdiag (a : Fin (Module.finrank ℝ E)) :
      inner ℝ (T (stdOrthonormalBasis ℝ E a))
        (stdOrthonormalBasis ℝ E a) = 0 := by
    have h := hsk (stdOrthonormalBasis ℝ E a) (stdOrthonormalBasis ℝ E a)
    have hc := real_inner_comm (stdOrthonormalBasis ℝ E a)
      (T (stdOrthonormalBasis ℝ E a))
    linarith only [h, hc]
  simp only [inner_sub_left, real_inner_smul_left, hdiag, mul_zero,
    sub_zero]
  exact basis_skew_sum T hsk w v

omit [Nontrivial E] in
theorem plain_wedge_ricci (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ
        (inner ℝ (stdOrthonormalBasis ℝ E a) w • v -
          inner ℝ v w • stdOrthonormalBasis ℝ E a)
        (stdOrthonormalBasis ℝ E a)) =
      (1 - (Module.finrank ℝ E : ℝ)) * inner ℝ v w := by
  simp only [inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib]
  rw [basis_inner_sum]
  simp only [← Finset.mul_sum, basis_self_sum]
  ring

omit [Nontrivial E] in
theorem compactWedgeSum_ricci (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (compactWedgeSum S (stdOrthonormalBasis ℝ E a) v w)
        (stdOrthonormalBasis ℝ E a)) =
      (-(Module.finrank ℝ E : ℝ) - 2) * inner ℝ v w := by
  simp only [compactWedgeSum, inner_add_left, Finset.sum_add_distrib]
  rw [plain_wedge_ricci, transformed_wedge_ricci S.I S.I_skew,
    transformed_wedge_ricci S.J S.J_skew,
    transformed_wedge_ricci S.K S.K_skew]
  ring

theorem sourceRH_ricci (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ
        (synth S (fun t => inner ℝ
          (quaternionicGenerator S t (stdOrthonormalBasis ℝ E a)) v) w)
        (stdOrthonormalBasis ℝ E a)) =
      -3 * inner ℝ v w := by
  simp only [synth_apply, Fin.sum_univ_three, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib]
  simp only [quaternionicGenerator]
  change (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (S.I (stdOrthonormalBasis ℝ E a)) v *
        inner ℝ (S.I w) (stdOrthonormalBasis ℝ E a)) +
      (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (S.J (stdOrthonormalBasis ℝ E a)) v *
        inner ℝ (S.J w) (stdOrthonormalBasis ℝ E a)) +
      (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (S.K (stdOrthonormalBasis ℝ E a)) v *
        inner ℝ (S.K w) (stdOrthonormalBasis ℝ E a)) = _
  rw [basis_skew_sum S.I S.I_skew,
    basis_skew_sum S.J S.J_skew,
    basis_skew_sum S.K S.K_skew]
  rw [real_inner_comm w v]
  ring

/-- The scalar quaternionic curvature model at normalization
`κ = 16n(n+2)`. It is exactly `-2 R_H - upperSquare`, where
`upperSquare = 2 R_E` in the real source representation. -/
def scalarModelR0 (u v : E) : E →L[ℝ] E :=
  (-2 : ℝ) • synth S (fun t => inner ℝ (quaternionicGenerator S t u) v) -
    upperSquare S u v

/-- Direct Ricci contraction of the source model: `Ric = 4(n+2) g` since
`dim_ℝ E = 4n`. This is an algebraic computation, independent of KSW. -/
theorem scalarModelR0_ricci (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (scalarModelR0 S (stdOrthonormalBasis ℝ E a) v w)
        (stdOrthonormalBasis ℝ E a)) =
      ((Module.finrank ℝ E : ℝ) + 8) * inner ℝ v w := by
  simp only [scalarModelR0, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_left, real_inner_smul_left,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sourceRH_ricci S]
  simp only [upperSquare_apply_compactWedgeSum]
  rw [compactWedgeSum_ricci S]
  ring

end
end QuaternionicSymmetry.QuaternionicKSWModelRicci
