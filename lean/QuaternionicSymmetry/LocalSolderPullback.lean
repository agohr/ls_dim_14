import QuaternionicSymmetry.ImmersionHessianCalculus

/-! The torsion equation pulls back through a smooth map of different
dimensions using its actual derivative and symmetric second derivative. -/
namespace QuaternionicSymmetry.LocalSolderPullback
open ImmersionHessianCalculus
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def solder (T : E → E →L[ℝ] E) (f : F → E) (y : F) : F →L[ℝ] E :=
  (T (f y)).comp (fderiv ℝ f y)

theorem differentiableAt_solder (T : E → E →L[ℝ] E) (f : F → E) (y : F)
    (hT : DifferentiableAt ℝ T (f y)) (hf : ContDiffAt ℝ 2 f y) :
    DifferentiableAt ℝ (solder T f) y :=
  (hT.comp y (hf.differentiableAt (by norm_num))).clm_comp
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem derivative_solder (T : E → E →L[ℝ] E) (f : F → E) (y : F)
    (hT : DifferentiableAt ℝ T (f y)) (hf : ContDiffAt ℝ 2 f y) (u v : F) :
    fderiv ℝ (solder T f) y u v =
      fderiv ℝ T (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) +
        T (f y) (fderiv ℝ (fderiv ℝ f) y u v) := by
  have h := solder_covariance_derivative (solder T f)
    (fun _ : F => ContinuousLinearMap.id ℝ F) T f y
    (differentiableAt_solder T f y hT hf) (differentiableAt_const _) hT hf
    (Filter.Eventually.of_forall (fun z => by ext v; rfl)) u v
  simpa only [ContinuousLinearMap.id_apply,fderiv_const_apply,ContinuousLinearMap.zero_apply,
    map_zero,add_zero] using h

theorem torsion (T : E → E →L[ℝ] E) (f : F → E) (y : F)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hT : DifferentiableAt ℝ T (f y)) (hf : ContDiffAt ℝ 2 f y)
    (hΓ : ∀ u v, fderiv ℝ T (f y) u v - fderiv ℝ T (f y) v u +
      Γ u (T (f y) v) - Γ v (T (f y) u) = 0) (u v : F) :
    fderiv ℝ (solder T f) y u v - fderiv ℝ (solder T f) y v u +
      Γ (fderiv ℝ f y u) (solder T f y v) - Γ (fderiv ℝ f y v) (solder T f y u) = 0 := by
  rw [derivative_solder T f y hT hf,derivative_solder T f y hT hf,
    (hf.isSymmSndFDerivAt (by norm_num)).eq v u]
  have h := hΓ (fderiv ℝ f y u) (fderiv ℝ f y v)
  change _ + Γ (fderiv ℝ f y u) (T (f y) (fderiv ℝ f y v)) -
    Γ (fderiv ℝ f y v) (T (f y) (fderiv ℝ f y u)) = 0
  linear_combination (norm := module) h

end
end QuaternionicSymmetry.LocalSolderPullback
