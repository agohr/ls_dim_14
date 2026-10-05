import QuaternionicSymmetry.GeneralImmersionChartPullbackMetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! First derivative of the literal chartwise pullback pairing of a
C² immersion, expressed by its symmetric ambient Hessian. -/

namespace QuaternionicSymmetry.GeneralImmersionChartMetricJet

open scoped ContDiff Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_ambient_pullback_pairing
    (f : E → V) (g : V →L[ℝ] V →L[ℝ] ℝ)
    (y u v w : E) (hf : ContDiffAt ℝ 2 f y) :
    let F := fderiv ℝ f
    let H := fderiv ℝ F y
    fderiv ℝ (fun z => g (F z v) (F z w)) y u =
      g (H u v) (F y w) + g (F y v) (H u w) := by
  let F := fderiv ℝ f
  let H := fderiv ℝ F y
  have hF : DifferentiableAt ℝ F y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFv : DifferentiableAt ℝ (fun z => F z v) y :=
    hF.clm_apply (differentiableAt_const _)
  have hFw : DifferentiableAt ℝ (fun z => F z w) y :=
    hF.clm_apply (differentiableAt_const _)
  have hgFv : DifferentiableAt ℝ (fun z => g (F z v)) y :=
    g.differentiableAt.comp y hFv
  change fderiv ℝ (fun z => (g (F z v)) (F z w)) y u = _
  rw [fderiv_clm_apply hgFv hFw]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hcomp := fderiv_comp y g.differentiableAt hFv
  change fderiv ℝ (fun z => g (F z v)) y = _ at hcomp
  rw [hcomp, g.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply hF (differentiableAt_const v),
    fderiv_clm_apply hF (differentiableAt_const w)]
  simp [F]
  abel

end
end QuaternionicSymmetry.GeneralImmersionChartMetricJet
