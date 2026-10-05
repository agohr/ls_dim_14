import QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! A smooth inverse chart on an open domain, including smoothness at every
point of its target. -/
namespace QuaternionicSymmetry.SmoothInverseChart
open scoped Manifold ContDiff Topology
open Filter Set
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_inverse_chart {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U)
    (D : E ≃L[ℝ] F) (hD : HasFDerivAt f (D : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ e.source ⊆ U ∧
      (e : E → F) = f ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  have hc : ContinuousAt (fderiv ℝ f) x :=
    (hfx.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ ∞ by decide)).continuousAt
  have hevent : ∀ᶠ y in 𝓝 x,
      fderiv ℝ f y ∈ Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) :=
    hc.eventually (ContinuousLinearEquiv.isOpen.mem_nhds ⟨D,hD.fderiv.symm⟩)
  obtain ⟨V,hVsub,hVopen,hxV⟩ := mem_nhds_iff.mp hevent
  let e₀ := hfx.toOpenPartialHomeomorph f hD (by simp)
  let e := e₀.restr (U ∩ V)
  have hsub : e.source ⊆ U := by
    intro y hy
    exact (interior_subset hy.2).1
  have hsubV : e.source ⊆ V := by
    intro y hy
    exact (interior_subset hy.2).2
  have heq : (e : E → F) = f := rfl
  have hforward : ContDiffOn ℝ ∞ e e.source := hf.mono hsub
  refine ⟨e,?_,hsub,heq,hforward,?_⟩
  · exact ⟨hfx.mem_toOpenPartialHomeomorph_source hD (by simp),
      by simpa only [(hU.inter hVopen).interior_eq] using And.intro hx hxV⟩
  · intro y hy
    have hz := e.symm_mapsTo hy
    obtain ⟨D',hD'⟩ := hVsub (hsubV hz)
    have hsm := hf.contDiffAt (hU.mem_nhds (hsub hz))
    apply (e.contDiffAt_symm hy (f₀' := D') ?_ ?_).contDiffWithinAt
    · change HasFDerivAt f (D' : E →L[ℝ] F) (e.symm y)
      rw [hD']
      exact (hsm.differentiableAt (by simp)).hasFDerivAt
    · exact hsm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_manifold_inverse_chart {f : M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f U)
    {x : M} (hx : x ∈ U) (D : E ≃L[ℝ] F)
    (hD : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x = (D : E →L[ℝ] F)) :
    ∃ e : OpenPartialHomeomorph M F, x ∈ e.source ∧ e.source ⊆ U ∧
      Set.EqOn e f e.source ∧
      ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e.symm e.target := by
  let c := chartAt E x
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.continuousOn_symm.isOpen_inter_preimage c.open_target hU
  have hcx : c x ∈ V := ⟨c.map_source (mem_chart_source E x), by
    change c.symm (c x) ∈ U
    rwa [c.left_inv (mem_chart_source E x)]⟩
  have hsm : ContDiffOn ℝ ∞ (f ∘ c.symm) V := by
    exact (hf.comp (contMDiffOn_chart_symm.mono Set.inter_subset_left)
      (fun y hy => hy.2)).contDiffOn
  have hd : HasFDerivAt (f ∘ c.symm) (D : E →L[ℝ] F) (c x) := by
    have h := ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
      (by simp)).hasMFDerivAt.2
    simpa [writtenInExtChartAt, extChartAt, hD, c] using h
  obtain ⟨d,hxd,hdV,hdf,hdsm,hdsym⟩ := exists_inverse_chart hV hsm hcx D hd
  let e := c.trans d
  have hsub : e.source ⊆ U := by
    intro y hy
    have hh := (hdV hy.2).2
    change c.symm (c y) ∈ U at hh
    rwa [c.left_inv hy.1] at hh
  have heq : Set.EqOn e f e.source := by
    intro y hy
    change d (c y) = f y
    rw [hdf]
    exact congrArg f (c.left_inv hy.1)
  refine ⟨e,⟨mem_chart_source E x,hxd⟩,hsub,heq,?_,?_⟩
  · exact (hf.mono hsub).congr heq
  · exact contMDiffOn_chart_symm.comp
      (hdsym.contMDiffOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

end
end QuaternionicSymmetry.SmoothInverseChart
