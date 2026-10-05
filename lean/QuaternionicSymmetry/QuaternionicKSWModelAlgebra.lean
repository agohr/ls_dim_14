import QuaternionicSymmetry.QuaternionicKSWModelRicci

/-! Algebraic Riemann symmetries and bilinearity of the explicit scalar
quaternionic curvature model. -/
namespace QuaternionicSymmetry.QuaternionicKSWModelAlgebra
open QuaternionicKSWModelRicci QuaternionicKSWUpperModel
open QuaternionicStandardSolderSquare
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)

theorem model_apply (u v w : E) : scalarModelR0 S u v w =
    (-2 : ℝ) • (inner ℝ (S.I u) v • S.I w + inner ℝ (S.J u) v • S.J w +
      inner ℝ (S.K u) v • S.K w) - compactWedgeSum S u v w := by
  simp only [scalarModelR0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    upperSquare_apply_compactWedgeSum, synth_apply, Fin.sum_univ_three,
    ContinuousLinearMap.add_apply, quaternionicGenerator]
  rfl

theorem model_add_left (u v z : E) : scalarModelR0 S (u + v) z =
    scalarModelR0 S u z + scalarModelR0 S v z := by
  ext w
  simp only [ContinuousLinearMap.add_apply, model_apply, compactWedgeSum,
    map_add, inner_add_left, add_smul, smul_add]
  module

theorem model_smul_left (c : ℝ) (u v : E) : scalarModelR0 S (c • u) v =
    c • scalarModelR0 S u v := by
  ext w
  simp only [ContinuousLinearMap.smul_apply, model_apply, compactWedgeSum,
    map_smul, real_inner_smul_left]
  module

theorem model_add_right (u v z : E) : scalarModelR0 S u (v + z) =
    scalarModelR0 S u v + scalarModelR0 S u z := by
  ext w
  simp only [ContinuousLinearMap.add_apply, model_apply, compactWedgeSum,
    map_add, inner_add_left, inner_add_right, add_smul, smul_add]
  module

theorem model_smul_right (c : ℝ) (u v : E) : scalarModelR0 S u (c • v) =
    c • scalarModelR0 S u v := by
  ext w
  simp only [ContinuousLinearMap.smul_apply, model_apply, compactWedgeSum,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  module

def modelLinear : E →ₗ[ℝ] E →ₗ[ℝ] (E →L[ℝ] E) :=
  LinearMap.mk₂ ℝ (scalarModelR0 S) (model_add_left S) (model_smul_left S)
    (model_add_right S) (fun c u v => model_smul_right S c u v)

def modelBilinear : E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  ({ toFun := fun u => (modelLinear S u).toContinuousLinearMap
     map_add' := by
       intro u v
       apply ContinuousLinearMap.ext
       intro w
       exact model_add_left S u v w
     map_smul' := by
       intro c u
       apply ContinuousLinearMap.ext
       intro w
       exact model_smul_left S c u w } :
    E →ₗ[ℝ] E →L[ℝ] E →L[ℝ] E).toContinuousLinearMap

theorem modelBilinear_apply (u v : E) : modelBilinear S u v = scalarModelR0 S u v := rfl

private theorem qskew (T : E ≃ₗᵢ[ℝ] E)
    (hT : ∀ u v, inner ℝ (T u) v = -inner ℝ u (T v)) (u v : E) :
    inner ℝ (T u) v = -inner ℝ (T v) u := by rw [hT, real_inner_comm]

theorem model_skew_first (u v : E) : scalarModelR0 S u v = -scalarModelR0 S v u := by
  ext w
  simp only [ContinuousLinearMap.neg_apply, model_apply, compactWedgeSum,
    qskew S.I S.I_skew v u, qskew S.J S.J_skew v u, qskew S.K S.K_skew v u]
  module

theorem model_skew_last (u v w z : E) :
    inner ℝ (scalarModelR0 S u v w) z = -inner ℝ (scalarModelR0 S u v z) w := by
  simp only [model_apply, compactWedgeSum, inner_sub_left, inner_add_left,
    real_inner_smul_left, qskew S.I S.I_skew z w,
    qskew S.J S.J_skew z w, qskew S.K S.K_skew z w,
    real_inner_comm u w, real_inner_comm v w, real_inner_comm u z, real_inner_comm v z]
  ring

theorem model_first_bianchi (u v w : E) :
    scalarModelR0 S u v w + scalarModelR0 S v w u + scalarModelR0 S w u v = 0 := by
  simp only [model_apply, compactWedgeSum,
    qskew S.I S.I_skew v u, qskew S.I S.I_skew w u, qskew S.I S.I_skew w v,
    qskew S.J S.J_skew v u, qskew S.J S.J_skew w u, qskew S.J S.J_skew w v,
    qskew S.K S.K_skew v u, qskew S.K S.K_skew w u, qskew S.K S.K_skew w v,
    real_inner_comm v u, real_inner_comm w u, real_inner_comm w v]
  module

end
end QuaternionicSymmetry.QuaternionicKSWModelAlgebra
