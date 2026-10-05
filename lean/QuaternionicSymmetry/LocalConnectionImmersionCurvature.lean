import QuaternionicSymmetry.LocalConnectionBianchi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Curvature intertwining for a parallel rectangular frame map. -/
namespace QuaternionicSymmetry.LocalConnectionImmersionCurvature
open LocalConnection LocalConnectionBianchi Filter
open scoped ContDiff Topology
noncomputable section
variable {X E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_apply (B : X → F →L[ℝ] E) (v : X → F) (y u : X)
    (hB : DifferentiableAt ℝ B y) (hv : DifferentiableAt ℝ v y) :
    fderiv ℝ (fun z => B z (v z)) y u = B y (fderiv ℝ v y u) + fderiv ℝ B y u (v y) := by
  rw [fderiv_clm_apply hB hv]
  rfl

theorem curvature_intertwines
    (B : X → F →L[ℝ] E) (Γ : X → X →L[ℝ] E →L[ℝ] E)
    (D : X → X →L[ℝ] F →L[ℝ] F) (y : X)
    (hB : ContDiffAt ℝ 2 B y) (hΓ : DifferentiableAt ℝ Γ y)
    (hD : DifferentiableAt ℝ D y)
    (hcov : ∀ᶠ z in 𝓝 y, ∀ u v, fderiv ℝ B z u v =
      B z (D z u v) - Γ z u (B z v)) (u v : X) (w : F) :
    curvature Γ y u v (B y w) = B y (curvature D y u v w) := by
  have hb := hB.differentiableAt (by norm_num)
  have hb' := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (a b : X) : fderiv ℝ (fderiv ℝ B) y a b w =
      B y (fderiv ℝ D y a b w) + fderiv ℝ B y a (D y b w) -
        (Γ y b (fderiv ℝ B y a w) + fderiv ℝ Γ y a b (B y w)) := by
    have hDb := hD.clm_apply (differentiableAt_const b)
    have hDbw := hDb.clm_apply (differentiableAt_const w)
    have hΓb := hΓ.clm_apply (differentiableAt_const b)
    have hbw := hb.clm_apply (differentiableAt_const w)
    have hh : (fun z => fderiv ℝ B z b w) =ᶠ[𝓝 y]
        (fun z => B z (D z b w) - Γ z b (B z w)) :=
      hcov.mono (fun z hz => hz b w)
    have hd := congrArg (fun A : X →L[ℝ] E => A a) hh.fderiv_eq
    rw [fderiv_fun_sub (hb.clm_apply hDbw) (hΓb.clm_apply hbw)] at hd
    simpa only [fderiv_eval_const (hb'.clm_apply (differentiableAt_const b)),
      fderiv_eval_const hb',ContinuousLinearMap.sub_apply,
      derivative_apply B (fun z => D z b w) y a hb hDbw,
      derivative_apply (fun z => Γ z b) (fun z => B z w) y a hΓb hbw,
      fderiv_eval_const hDb,fderiv_eval_const hD,fderiv_eval_const hb,
      fderiv_eval_const hΓ] using hd
  have huv := he u v
  have hvu := he v u
  rw [(hB.isSymmSndFDerivAt (by norm_num)).eq v u] at hvu
  have hc := hcov.self_of_nhds
  simp only [hc,map_sub] at huv hvu
  simp only [curvature_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply,map_sub,map_add]
  linear_combination (norm := module) huv - hvu

end
end QuaternionicSymmetry.LocalConnectionImmersionCurvature
