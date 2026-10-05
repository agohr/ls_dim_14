import QuaternionicSymmetry.LocalConnectionImmersionCurvature

/-! Curvature pullback through a smooth map between different model spaces. -/
namespace QuaternionicSymmetry.LocalConnectionMapPullback
open LocalConnection LocalConnectionBianchi LocalConnectionImmersionCurvature
open scoped ContDiff
noncomputable section
variable {E F R : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedRing R] [NormedAlgebra ℝ R]

def pullback (Γ : E → E →L[ℝ] R) (f : F → E) (y : F) : F →L[ℝ] R :=
  (Γ (f y)).comp (fderiv ℝ f y)

theorem differentiableAt_pullback (Γ : E → E →L[ℝ] R) (f : F → E) (y : F)
    (hΓ : DifferentiableAt ℝ Γ (f y)) (hf : ContDiffAt ℝ 2 f y) :
    DifferentiableAt ℝ (pullback Γ f) y :=
  (hΓ.comp y (hf.differentiableAt (by norm_num))).clm_comp
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem derivative_pullback (Γ : E → E →L[ℝ] R) (f : F → E) (y : F)
    (hΓ : DifferentiableAt ℝ Γ (f y)) (hf : ContDiffAt ℝ 2 f y) (u v : F) :
    fderiv ℝ (pullback Γ f) y u v =
      fderiv ℝ Γ (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) +
        Γ (f y) (fderiv ℝ (fderiv ℝ f) y u v) := by
  have hf' := hf.differentiableAt (by norm_num)
  have hf'' := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg := hΓ.comp y hf'
  have hc : fderiv ℝ (fun z => Γ (f z)) y =
      (fderiv ℝ Γ (f y)).comp (fderiv ℝ f y) := fderiv_comp y hΓ hf'
  rw [← fderiv_eval_const (differentiableAt_pullback Γ f y hΓ hf) v u]
  change fderiv ℝ (fun z => Γ (f z) (fderiv ℝ f z v)) y u = _
  rw [derivative_apply (fun z => Γ (f z)) _ y u hg (hf''.clm_apply (differentiableAt_const v)),
    fderiv_eval_const hf'',hc]
  exact add_comm _ _

theorem curvature_pullback (Γ : E → E →L[ℝ] R) (f : F → E) (y : F)
    (hΓ : DifferentiableAt ℝ Γ (f y)) (hf : ContDiffAt ℝ 2 f y) (u v : F) :
    curvature (pullback Γ f) y u v =
      curvature Γ (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) := by
  rw [curvature_apply,derivative_pullback Γ f y hΓ hf,
    derivative_pullback Γ f y hΓ hf,(hf.isSymmSndFDerivAt (by norm_num)).eq v u,
    curvature_apply]
  simp only [pullback,ContinuousLinearMap.comp_apply]
  abel

end
end QuaternionicSymmetry.LocalConnectionMapPullback
