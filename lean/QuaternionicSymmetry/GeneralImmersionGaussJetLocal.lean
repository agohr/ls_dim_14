import QuaternionicSymmetry.GeneralImmersionGaussJet

/-! Neighborhood-level differentiated Gauss equation for a genuine
partial chart, with no global off-chart equality required. -/

namespace QuaternionicSymmetry.GeneralImmersionGaussJetLocal

open LocalConnectionBianchi
open scoped Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivative_projected_hessian_gauss_local
    (f : E → V) (π : E → V →L[ℝ] V)
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (y u v w : E)
    (hdF : DifferentiableAt ℝ (fderiv ℝ f) y)
    (hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) y)
    (hπ : DifferentiableAt ℝ π y)
    (hΓ : DifferentiableAt ℝ Γ y)
    (hGauss : ∀ᶠ z in 𝓝 y, ∀ a b,
      fderiv ℝ f z (Γ z a b) =
        π z (fderiv ℝ (fderiv ℝ f) z a b)) :
    (fderiv ℝ (fderiv ℝ f) y u) (Γ y v w) +
      (fderiv ℝ f y) ((fderiv ℝ Γ y u) v w) =
        (fderiv ℝ π y u) (fderiv ℝ (fderiv ℝ f) y v w) +
          π y ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y u) v w) := by
  let dF := fderiv ℝ f
  let H := fderiv ℝ dF
  have hΓvw : DifferentiableAt ℝ (fun z => Γ z v w) y :=
    (hΓ.clm_apply (differentiableAt_const v)).clm_apply
      (differentiableAt_const w)
  have hΓv : DifferentiableAt ℝ (fun z => Γ z v) y :=
    hΓ.clm_apply (differentiableAt_const v)
  have hHvw : DifferentiableAt ℝ (fun z => H z v w) y :=
    (hH.clm_apply (differentiableAt_const v)).clm_apply
      (differentiableAt_const w)
  have hHv : DifferentiableAt ℝ (fun z => H z v) y :=
    hH.clm_apply (differentiableAt_const v)
  have hfun : (fun z => dF z (Γ z v w)) =ᶠ[𝓝 y]
      (fun z => π z (H z v w)) :=
    hGauss.mono (fun z hz => hz v w)
  have hd : fderiv ℝ (fun z => dF z (Γ z v w)) y u =
      fderiv ℝ (fun z => π z (H z v w)) y u :=
    congrArg (fun L : E →L[ℝ] V => L u) hfun.fderiv_eq
  rw [fderiv_clm_apply hdF hΓvw,
    fderiv_clm_apply hπ hHvw] at hd
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hd
  rw [fderiv_eval_const hΓv w u, fderiv_eval_const hΓ v u,
    fderiv_eval_const hHv w u, fderiv_eval_const hH v u] at hd
  simp [dF, H] at hd
  simpa [add_comm, add_left_comm, add_assoc] using hd

end
end QuaternionicSymmetry.GeneralImmersionGaussJetLocal
