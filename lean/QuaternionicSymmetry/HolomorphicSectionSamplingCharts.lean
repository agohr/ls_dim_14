import QuaternionicSymmetry.HolomorphicLineCoreProjectiveHolomorphic
import QuaternionicSymmetry.FiniteHolomorphicSampling

/-! Compact coordinate balls for sampling genuine holomorphic line sections. -/
namespace QuaternionicSymmetry.HolomorphicSectionSamplingCharts
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLinePowers
open scoped Manifold ContDiff Topology
open Metric Set
noncomputable section

variable {B F : Type} [TopologicalSpace B] [T2Space B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L : LineCore.{0} (B := B) 𝓘(ℂ,F))

structure SamplingChart where
  point : B
  index : L.Index
  radius : ℝ
  radius_pos : 0 < radius
  outer_subset : closedBall (chartAt F point point) (3 * radius) ⊆
    (chartAt F point).target ∩ (chartAt F point).symm ⁻¹' L.core.baseSet index

namespace SamplingChart
variable {L} (c : SamplingChart L)

def center : F := chartAt F c.point c.point
def inner : Set B := (chartAt F c.point).symm '' closedBall c.center c.radius
def outer : Set B := (chartAt F c.point).symm '' closedBall c.center (3 * c.radius)
def inside : Set B := (chartAt F c.point).source ∩
  (chartAt F c.point) ⁻¹' ball c.center c.radius

theorem inner_sub_outer : c.inner ⊆ c.outer :=
  Set.image_mono (closedBall_subset_closedBall (by linarith [c.radius_pos]))

theorem outer_in_base : c.outer ⊆ L.core.baseSet c.index := by
  rintro x ⟨z,hz,rfl⟩
  exact (c.outer_subset hz).2

theorem compact_outer : IsCompact c.outer :=
  (isCompact_closedBall c.center (3 * c.radius)).image_of_continuousOn
    ((chartAt F c.point).continuousOn_symm.mono (fun _ hz => (c.outer_subset hz).1))

theorem compact_inner : IsCompact c.inner :=
  (isCompact_closedBall c.center c.radius).image_of_continuousOn
    ((chartAt F c.point).continuousOn_symm.mono (fun z hz =>
      (c.outer_subset (closedBall_subset_closedBall (by linarith [c.radius_pos]) hz)).1))

theorem open_inside : IsOpen c.inside :=
  (chartAt F c.point).continuousOn.isOpen_inter_preimage
    (chartAt F c.point).open_source isOpen_ball

theorem point_inside : c.point ∈ c.inside :=
  ⟨mem_chart_source F c.point,mem_ball_self c.radius_pos⟩

theorem inside_sub_inner : c.inside ⊆ c.inner := by
  intro x hx
  exact ⟨chartAt F c.point x,Metric.ball_subset_closedBall hx.2,
    (chartAt F c.point).left_inv hx.1⟩

def evaluation (z : F) : GlobalSections 𝓘(ℂ,F) L →ₗ[ℂ] ℂ where
  toFun s := chartEvaluation 𝓘(ℂ,F) L c.index ((chartAt F c.point).symm z) s
  map_add' s t := by
    exact map_add (L.core.coordChange _ _ _) _ _
  map_smul' a s := by
    exact map_smul (L.core.coordChange _ _ _) _ _

theorem holomorphic_evaluation (s : GlobalSections 𝓘(ℂ,F) L) :
    DifferentiableOn ℂ (fun z => c.evaluation z s) (ball c.center (3 * c.radius)) := by
  have hT : ball c.center (3 * c.radius) ⊆ (chartAt F c.point).target :=
    fun _ hz => (c.outer_subset (Metric.ball_subset_closedBall hz)).1
  have hL : ∀ z ∈ ball c.center (3 * c.radius),
      (chartAt F c.point).symm z ∈ L.core.baseSet c.index :=
    fun _ hz => (c.outer_subset (Metric.ball_subset_closedBall hz)).2
  exact ((contMDiffOn_chartEvaluation 𝓘(ℂ,F) L c.index s).comp
    (contMDiffOn_chart_symm.mono hT) hL).contDiffOn.differentiableOn (by simp)

end SamplingChart

theorem exists_samplingChart (x : B) : ∃ c : SamplingChart L, c.point = x := by
  let e := chartAt F x
  let U := e.target ∩ e.symm ⁻¹' L.core.baseSet (L.core.indexAt x)
  have hU : IsOpen U := e.continuousOn_symm.isOpen_inter_preimage
    e.open_target (L.core.isOpen_baseSet _)
  have hx : e x ∈ U := ⟨e.map_source (mem_chart_source F x), by
    change e.symm (e x) ∈ L.core.baseSet (L.core.indexAt x)
    rw [e.left_inv (mem_chart_source F x)]
    exact L.core.mem_baseSet_at x⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨⟨x,L.core.indexAt x,ε / 4,by positivity,?_⟩,rfl⟩
  exact (closedBall_subset_ball (by linarith)).trans hball

theorem finite_sampling_cover [CompactSpace B] :
    ∃ (I : Type) (_ : Fintype I) (c : I → SamplingChart L),
      ∀ x : B, ∃ i, x ∈ (c i).inner := by
  classical
  choose c hc using exists_samplingChart L
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : B => (c x).inside) (fun x => (c x).open_inside) (by
      intro x _
      exact mem_iUnion.mpr ⟨x,by simpa only [hc x] using (c x).point_inside⟩)
  refine ⟨s,inferInstance,fun x => c x,?_⟩
  intro x
  obtain ⟨y,hy,hx⟩ := mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨y,hy⟩,(c y).inside_sub_inner hx⟩

end
end QuaternionicSymmetry.HolomorphicSectionSamplingCharts
