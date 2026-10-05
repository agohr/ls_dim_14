import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Smoothness derived from the chart normal form in `IsImmersionAt`.
The corresponding Mathlib `IsSmoothEmbedding.contMDiff` declaration is still
`proof_wanted`, so this file never invokes it. -/
namespace QuaternionicSymmetry.ManifoldImmersionSmooth
open Manifold Set
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
/-- The chart normal form itself forces continuity at the immersion point. -/
theorem ofComplement_continuousAt
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : M → N} {x : M}
    (h : IsImmersionAtOfComplement C 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x) :
    ContinuousAt f x := by
  let a := h.domChart.extend 𝓘(ℝ,E)
  let b := h.codChart.extend 𝓘(ℝ,F)
  let g : E → F := fun u => h.equiv (u, 0)
  have hax : a x ∈ a.target := a.map_source (by
    simpa [a, OpenPartialHomeomorph.extend_source] using h.mem_domChart_source)
  have hbg : g (a x) ∈ b.target := h.target_subset_preimage_target hax
  have hg : Continuous g := by fun_prop
  have hga : ContinuousAt g (a x) := hg.continuousAt
  have haCont : ContinuousAt a x :=
    h.domChart.continuousAt_extend h.mem_domChart_source
  have hbInv : ContinuousAt b.symm (g (a x)) :=
    h.codChart.continuousAt_extend_symm' hbg
  have hbcomp : ContinuousAt (b.symm ∘ g) (a x) := hbInv.comp hga
  have hq : ContinuousAt (fun z : M => b.symm (g (a z))) x :=
    hbcomp.comp haCont
  have heq : f =ᶠ[𝓝 x] (fun z : M => b.symm (g (a z))) := by
    filter_upwards [h.domChart.extend_source_mem_nhds (I := 𝓘(ℝ,E))
      h.mem_domChart_source]
      with z hz
    have hz' : z ∈ h.domChart.source := by
      simpa [a, OpenPartialHomeomorph.extend_source] using hz
    have haz : a z ∈ a.target := a.map_source hz
    have hw := h.writtenInCharts haz
    have ha' : a.symm (a z) = z := a.left_inv hz
    change b (f (a.symm (a z))) = g (a z) at hw
    rw [ha'] at hw
    have hbz : f z ∈ b.source := by
      simpa [b, OpenPartialHomeomorph.extend_source] using
        h.source_subset_preimage_source hz'
    calc
      f z = b.symm (b (f z)) := (b.left_inv hbz).symm
      _ = b.symm (g (a z)) := congrArg b.symm hw
  exact hq.congr_of_eventuallyEq heq

/-- The immersion normal form gives the local coordinate smoothness; a
continuity premise supplies the remaining topological condition. -/
theorem ofComplement_contMDiffAt_of_continuousAt
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : M → N} {x : M}
    (h : IsImmersionAtOfComplement C 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x)
    (hc : ContinuousAt f x) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x := by
  change ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f Set.univ x
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas
    h.domChart_mem_maximalAtlas h.codChart_mem_maximalAtlas
    h.mem_domChart_source h.mem_codChart_source]
  simp only [Set.preimage_univ, Set.univ_inter, continuousWithinAt_univ]
  refine ⟨hc, ?_⟩
  let g : E → F := fun u => h.equiv (u, 0)
  have hg : ContDiff ℝ ∞ g := by
    fun_prop
  have ht : h.domChart.extend 𝓘(ℝ,E) x ∈
      (h.domChart.extend 𝓘(ℝ,E)).target := by
    apply PartialEquiv.map_source
    simpa only [OpenPartialHomeomorph.extend_source] using h.mem_domChart_source
  have heq :
      ((h.codChart.extend 𝓘(ℝ,F)) ∘ f ∘
        (h.domChart.extend 𝓘(ℝ,E)).symm) =ᶠ[𝓝
          (h.domChart.extend 𝓘(ℝ,E) x)] g :=
    by
      filter_upwards [(h.domChart.isOpen_extend_target.mem_nhds ht)]
        with u hu
      exact h.writtenInCharts hu
  have hgg : ContDiffWithinAt ℝ ∞ g (range 𝓘(ℝ,E))
      (h.domChart.extend 𝓘(ℝ,E) x) := hg.contDiffAt.contDiffWithinAt
  exact hgg.congr_of_eventuallyEq
    (Filter.Eventually.filter_mono (nhdsWithin_le_nhds) heq)
    heq.self_of_nhds

/-- A smooth embedding is smooth, proved from its immersion normal form
and topological embedding rather than Mathlib's admitted declaration. -/
theorem smoothEmbedding_contMDiff {f : M → N}
    (h : IsSmoothEmbedding 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f := by
  intro x
  exact ofComplement_contMDiffAt_of_continuousAt
    (h.isImmersion.isImmersionAt x).isImmersionAtOfComplement_complement
    h.isEmbedding.continuous.continuousAt

/-- A smooth immersion is smooth, with continuity obtained from the same
normal form. -/
theorem immersion_contMDiff {f : M → N}
    (h : IsImmersion 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f := by
  intro x
  let hx := (h.isImmersionAt x).isImmersionAtOfComplement_complement
  exact ofComplement_contMDiffAt_of_continuousAt hx (ofComplement_continuousAt hx)

end
end QuaternionicSymmetry.ManifoldImmersionSmooth
