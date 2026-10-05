import QuaternionicSymmetry.SubspaceSubmanifoldChart
import Mathlib.Topology.LocallyConstant.Basic

/-! Local smooth submanifold charts have the same dimension on overlaps.
Consequently their dimension is constant on a connected component. -/
namespace QuaternionicSymmetry.SubmanifoldChartDimension
open Set Filter SubspaceSubmanifoldChart
open scoped Manifold ContDiff Topology
noncomputable section

lemma finrank_eq_of_inverse_charts
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : OpenPartialHomeomorph F G)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {x : F} (hx : x ∈ e.source) : Module.finrank ℝ F = Module.finrank ℝ G := by
  have hf := (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hg := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have hl : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hr : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have hlD := hl.fderiv_eq (𝕜 := ℝ)
  have hrD := hr.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp _ hg hf,fderiv_id] at hlD
  have hf' : DifferentiableAt ℝ e (e.symm (e x)) := by rwa [e.left_inv hx]
  rw [fderiv_comp _ hf' hg,fderiv_id,e.left_inv hx] at hrD
  have hleft : Function.LeftInverse (fderiv ℝ e.symm (e x)) (fderiv ℝ e x) := by
    intro v
    exact congrArg (fun D : F →L[ℝ] F => D v) hlD
  have hright : Function.RightInverse (fderiv ℝ e.symm (e x)) (fderiv ℝ e x) := by
    intro v
    exact congrArg (fun D : G →L[ℝ] G => D v) hrD
  exact (LinearEquiv.ofBijective (fderiv ℝ e x).toLinearMap
    ⟨hleft.injective,hright.surjective⟩).finrank_eq

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

lemma chart_dimension_eq {S : Set M} {k l : ℕ}
    (C : LocalChart (I := I) S k) (D : LocalChart (I := I) S l)
    {x : S} (hxC : x ∈ C.chart.source) (hxD : x ∈ D.chart.source) : k = l := by
  have h := finrank_eq_of_inverse_charts (C.chart.symm.trans D.chart)
    (transition_smooth C D) (transition_smooth D C)
    (x := C.chart x) ⟨C.chart.map_source hxC,by
      change C.chart.symm (C.chart x) ∈ D.chart.source
      rwa [C.chart.left_inv hxC]⟩
  simpa using h

lemma dimension_constant {S : Set M} [PreconnectedSpace S]
    (d : S → ℕ) (C : ∀ x : S, LocalChart (I := I) S (d x))
    (hC : ∀ x, x ∈ (C x).chart.source) (x y : S) : d x = d y := by
  have hloc : IsLocallyConstant d := by
    apply (IsLocallyConstant.iff_exists_open d).mpr
    intro z
    refine ⟨(C z).chart.source,(C z).chart.open_source,hC z,?_⟩
    intro w hw
    exact chart_dimension_eq (C w) (C z) (hC w) hw
  exact hloc.apply_eq_of_preconnectedSpace x y

end
end QuaternionicSymmetry.SubmanifoldChartDimension
