import QuaternionicSymmetry.SmoothInverseChart

/-! The derivative of a smooth local chart with smooth inverse is an actual
continuous linear equivalence on every point of its source. -/
namespace QuaternionicSymmetry.SmoothChartDerivativeEquiv
open Set Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F H H' M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [IsManifold I ∞ M] [IsManifold J ∞ N]

lemma exists_derivative_equiv (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source) (hei : ContMDiffOn J I ∞ e.symm e.target)
    {x : M} (hx : x ∈ e.source) :
    ∃ D : E ≃L[ℝ] F, (D : E →L[ℝ] F) = mfderiv I J e x := by
  have hf := (he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hg := (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hx))).mdifferentiableAt (by simp)
  have hl : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hr : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have hlD := hl.mfderiv_eq (I := I) (I' := I)
  have hrD := hr.mfderiv_eq (I := J) (I' := J)
  rw [mfderiv_comp _ hg hf,mfderiv_id] at hlD
  have hf' : MDifferentiableAt I J e (e.symm (e x)) := by rwa [e.left_inv hx]
  rw [mfderiv_comp _ hf' hg,mfderiv_id,e.left_inv hx] at hrD
  let D : E ≃L[ℝ] F := {
    toLinearMap := (mfderiv I J e x).toLinearMap
    invFun := mfderiv J I e.symm (e x)
    left_inv := fun v => congrArg (fun A : E →L[ℝ] E => A v) hlD
    right_inv := fun v => congrArg (fun A : F →L[ℝ] F => A v) hrD
    continuous_toFun := (mfderiv I J e x).continuous
    continuous_invFun := (mfderiv J I e.symm (e x)).continuous }
  exact ⟨D,rfl⟩

end
end QuaternionicSymmetry.SmoothChartDerivativeEquiv
