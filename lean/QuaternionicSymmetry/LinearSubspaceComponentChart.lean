import QuaternionicSymmetry.SubspaceSubmanifoldChart
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Topology

/-! A local linear-subspace description also supplies charts on each literal
connected component, by shrinking to a convex ball. -/
namespace QuaternionicSymmetry.LinearSubspaceComponentChart
open Set SubspaceSubmanifoldChart
open scoped Manifold ContDiff Topology
noncomputable section

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

lemma exists_component_chart {S : Set M} {x z : M}
    (hz : z ∈ connectedComponentIn S x)
    (e : OpenPartialHomeomorph M E) (W : Submodule ℝ E)
    (he : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ,E) I ∞ e.symm e.target)
    (hze : z ∈ e.source) (he0 : e z = 0)
    (h : e.IsImage S (W : Set E)) :
    ∃ C : LocalChart (I := I) (connectedComponentIn S x) (Module.finrank ℝ W),
      (⟨z,hz⟩ : connectedComponentIn S x) ∈ C.chart.source := by
  have h0 : (0 : E) ∈ e.target := he0 ▸ e.map_source hze
  obtain ⟨r,hr,hrT⟩ := Metric.isOpen_iff.mp e.open_target 0 h0
  let d := (e.symm.restrOpen (Metric.ball 0 r) Metric.isOpen_ball).symm
  have hdsource : d.source ⊆ e.source := inter_subset_left
  have hdtarget : d.target = Metric.ball 0 r := inter_eq_right.mpr hrT
  have hzd : z ∈ d.source := by
    exact ⟨hze,by change e z ∈ Metric.ball 0 r; simpa [he0] using hr⟩
  have hconn : IsPreconnected (e.symm '' (Metric.ball 0 r ∩ (W : Set E))) := by
    apply ((convex_ball (0 : E) r).inter W.convex).isPreconnected.image
    exact e.continuousOn_symm.mono (fun y hy => hrT hy.1)
  have hzimage : z ∈ e.symm '' (Metric.ball 0 r ∩ (W : Set E)) := by
    refine ⟨0,⟨by simpa using hr,W.zero_mem⟩,?_⟩
    rw [← he0,e.left_inv hze]
  have hsubS : e.symm '' (Metric.ball 0 r ∩ (W : Set E)) ⊆ S := by
    rintro _ ⟨v,hv,rfl⟩
    exact (h.symm_apply_mem_iff (hrT hv.1)).mpr hv.2
  have himageComp : e.symm '' (Metric.ball 0 r ∩ (W : Set E)) ⊆ connectedComponentIn S x := by
    have hh := hconn.subset_connectedComponentIn hzimage hsubS
    rwa [← connectedComponentIn_eq hz] at hh
  have hd : d.IsImage (connectedComponentIn S x) (W : Set E) := by
    intro y hy
    constructor
    · intro hyW
      have hyball : e y ∈ Metric.ball 0 r := hy.2
      apply himageComp
      refine ⟨e y,⟨hyball,hyW⟩,e.left_inv hy.1⟩
    · intro hyC
      exact (h.apply_mem_iff hy.1).mpr (connectedComponentIn_subset S x hyC)
  letI : Nonempty (connectedComponentIn S x) := ⟨⟨z,hz⟩⟩
  obtain ⟨C,hC⟩ := exists_local_chart d W hd (he.mono hdsource)
    (hei.mono inter_subset_left)
  exact ⟨C,by rw [hC]; exact hzd⟩

end
end QuaternionicSymmetry.LinearSubspaceComponentChart
