import QuaternionicSymmetry.LocalConnectionCovariantRiemannAlgebra

/-! Metric skewness of the covariant derivative of an endomorphism-valued
curvature form. -/
namespace QuaternionicSymmetry.LocalConnectionCovariantMetricSkew
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

theorem fderiv_variable_metric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (F : E → E) (x a z : E)
    (hg : DifferentiableAt ℝ g x) (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y => g y (F y) z) x a =
      g x (fderiv ℝ F x a) z + fderiv ℝ g x a (F x) z := by
  have hgf : DifferentiableAt ℝ (fun y => g y (F y)) x :=
    hg.clm_apply hF
  rw [fderiv_eval_const hgf z a, fderiv_clm_apply hg hF]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

/-- If the coordinate connection preserves a varying metric and curvature
is skew for that metric on a neighborhood, its full covariant derivative is
skew in the two metric slots. -/
theorem covariantCurvatureDerivative_metric_skew
    (Γ : Form (E := E) (A := E →L[ℝ] E))
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x a u v w z : E)
    (hg : DifferentiableAt ℝ g x)
    (hF : DifferentiableAt ℝ (fun y => curvature Γ y u v) x)
    (hmetric : ∀ b c : E,
      fderiv ℝ g x a b c =
        g x (Γ x a b) c + g x b (Γ x a c))
    (hskew : ∀ b c : E,
      (fun y => g y (curvature Γ y u v b) c +
        g y b (curvature Γ y u v c)) =ᶠ[𝓝 x] fun _ => 0) :
    g x (covariantCurvatureDerivative Γ x a u v w) z +
      g x w (covariantCurvatureDerivative Γ x a u v z) = 0 := by
  let F : E → E := fun y => curvature Γ y u v w
  let H : E → E := fun y => curvature Γ y u v z
  have hFw : DifferentiableAt ℝ F x :=
    hF.clm_apply (differentiableAt_const _)
  have hHz : DifferentiableAt ℝ H x :=
    hF.clm_apply (differentiableAt_const _)
  have hfirst : DifferentiableAt ℝ (fun y => g y (F y) z) x :=
    (hg.clm_apply hFw).clm_apply (differentiableAt_const _)
  have hsecond : DifferentiableAt ℝ (fun y => g y w (H y)) x :=
    ((hg.clm_apply (differentiableAt_const _)).clm_apply hHz)
  have hd := (hskew w z).fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_add hfirst hsecond] at hd
  have hdA := congrArg (fun L : E →L[ℝ] ℝ => L a) hd
  simp only [ContinuousLinearMap.add_apply, fderiv_const_apply,
    ContinuousLinearMap.zero_apply] at hdA
  rw [fderiv_variable_metric g F x a z hg hFw] at hdA
  have hsecondDeriv :
      fderiv ℝ (fun y => g y w (H y)) x a =
        fderiv ℝ g x a w (H x) + g x w (fderiv ℝ H x a) := by
    rw [fderiv_clm_apply (hg.clm_apply (differentiableAt_const _)) hHz]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [fderiv_eval_const hg w a]
    abel
  rw [hsecondDeriv] at hdA
  rw [hmetric (F x) z, hmetric w (H x)] at hdA
  have hs₁ := (hskew w (Γ x a z)).self_of_nhds
  have hs₂ := (hskew (Γ x a w) z).self_of_nhds
  change g x (curvature Γ x u v w) (Γ x a z) +
      g x w (curvature Γ x u v (Γ x a z)) = 0 at hs₁
  change g x (curvature Γ x u v (Γ x a w)) z +
      g x (Γ x a w) (curvature Γ x u v z) = 0 at hs₂
  dsimp only [F, H] at hdA
  rw [fderiv_eval_const hF w a, fderiv_eval_const hF z a] at hdA
  simp only [covariantCurvatureDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  linear_combination hdA - hs₁ - hs₂

end
end QuaternionicSymmetry.LocalConnectionCovariantMetricSkew
