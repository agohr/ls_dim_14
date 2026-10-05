import QuaternionicSymmetry.GeneralImmersionHessianSymmetry
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! A fixed real-linear ambient equation on a C² immersion holds on its
true Hessian as well as on its first derivative. -/

namespace QuaternionicSymmetry.GeneralImmersionHessianLinearConstraint

open scoped ContDiff Topology

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem hessian_linear_constraint
    (f : E → V) (L : V →L[ℝ] W) (y u v : E)
    (hf : ContDiffAt ℝ 2 f y)
    (h : ∀ z, L (f z) = 0) :
    L (fderiv ℝ (fderiv ℝ f) y u v) = 0 := by
  let T : (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] W) :=
    ContinuousLinearMap.compL ℝ E V W L
  have hfun : L ∘ f = fun _ => (0 : W) := funext h
  have hfirst : (fun z => T (fderiv ℝ f z)) =ᶠ[𝓝 y]
      (fun _ => (0 : E →L[ℝ] W)) := by
    filter_upwards [hf.eventually (by decide)] with z hz
    have hd := fderiv_comp z L.differentiableAt
      (hz.differentiableAt (by norm_num))
    rw [L.fderiv] at hd
    change fderiv ℝ (L ∘ f) z = L.comp (fderiv ℝ f z) at hd
    rw [hfun] at hd
    simpa [T] using hd.symm
  have hzero : fderiv ℝ (fun z => T (fderiv ℝ f z)) y = 0 := by
    rw [hfirst.fderiv_eq]
    simp
  have hF : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := fderiv_comp y T.differentiableAt hF
  change fderiv ℝ (fun z => T (fderiv ℝ f z)) y =
    (fderiv ℝ T (fderiv ℝ f y)).comp (fderiv ℝ (fderiv ℝ f) y) at hd
  rw [T.fderiv] at hd
  have hu := congrArg (fun A : E →L[ℝ] (E →L[ℝ] W) => A u) (hzero.symm.trans hd)
  have hv := congrArg (fun A : E →L[ℝ] W => A v) hu
  simpa only [ContinuousLinearMap.comp_apply, T,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.zero_apply] using hv.symm

end QuaternionicSymmetry.GeneralImmersionHessianLinearConstraint
