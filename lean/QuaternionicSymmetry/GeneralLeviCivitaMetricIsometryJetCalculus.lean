import QuaternionicSymmetry.GeneralLeviCivitaIsometryChartMetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The exact first-jet product rule for an isometry written using an
adapted solder field and its genuine chart derivative. This is a calculus
lemma; its input map and field will be the already constructed projector
isometry and tangent frame. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaMetricIsometryJetCalculus

open scoped Manifold ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_inner_solder_chart_map
    (F : E → E) (T : E → E →L[ℝ] E) (y u v w : E)
    (hF : ContDiffAt ℝ 2 F y)
    (hT : DifferentiableAt ℝ T (F y)) :
    let R := fderiv ℝ F
    let dR := fderiv ℝ R y
    fderiv ℝ
      (fun z => inner ℝ (T (F z) (R z v)) (T (F z) (R z w))) y u =
      inner ℝ
        ((fderiv ℝ T (F y)) (R y u) (R y v) + T (F y) (dR u v))
        (T (F y) (R y w)) +
      inner ℝ (T (F y) (R y v))
        ((fderiv ℝ T (F y)) (R y u) (R y w) + T (F y) (dR u w)) := by
  dsimp only
  let R := fderiv ℝ F
  let V := fun z : E => T (F z) (R z v)
  let W := fun z : E => T (F z) (R z w)
  have hFd : DifferentiableAt ℝ F y := hF.differentiableAt (by norm_num)
  have hR : DifferentiableAt ℝ R y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hTF : DifferentiableAt ℝ (T ∘ F) y := hT.comp y hFd
  have hRv : DifferentiableAt ℝ (fun z => R z v) y :=
    hR.clm_apply (differentiableAt_const _)
  have hRw : DifferentiableAt ℝ (fun z => R z w) y :=
    hR.clm_apply (differentiableAt_const _)
  have hV : DifferentiableAt ℝ V y := hTF.clm_apply hRv
  have hW : DifferentiableAt ℝ W y := hTF.clm_apply hRw
  change fderiv ℝ (fun z => inner ℝ (V z) (W z)) y u = _
  rw [fderiv_inner_apply ℝ hV hW u]
  have hdTF : fderiv ℝ (T ∘ F) y =
      (fderiv ℝ T (F y)).comp (R y) := fderiv_comp y hT hFd
  have hdRv : fderiv ℝ (fun z => R z v) y u = fderiv ℝ R y u v := by
    rw [fderiv_clm_apply hR (differentiableAt_const _)]
    simp
  have hdRw : fderiv ℝ (fun z => R z w) y u = fderiv ℝ R y u w := by
    rw [fderiv_clm_apply hR (differentiableAt_const _)]
    simp
  have hdV : fderiv ℝ V y u =
      (fderiv ℝ T (F y)) (R y u) (R y v) + T (F y) (fderiv ℝ R y u v) := by
    rw [show V = fun z => (T ∘ F) z ((fun z => R z v) z) from rfl,
      fderiv_clm_apply hTF hRv, hdTF]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Function.comp_apply]
    rw [hdRv]
    abel
  have hdW : fderiv ℝ W y u =
      (fderiv ℝ T (F y)) (R y u) (R y w) + T (F y) (fderiv ℝ R y u w) := by
    rw [show W = fun z => (T ∘ F) z ((fun z => R z w) z) from rfl,
      fderiv_clm_apply hTF hRw, hdTF]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Function.comp_apply]
    rw [hdRw]
    abel
  simp only [hdV, hdW, V, W, R]
  abel

end
end QuaternionicSymmetry.GeneralLeviCivitaMetricIsometryJetCalculus
