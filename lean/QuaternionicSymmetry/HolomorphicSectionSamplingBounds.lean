import QuaternionicSymmetry.HolomorphicSectionSamplingCharts

/-! Uniform comparison of section coefficients on a finite compact chart
cover. The constants depend on transition functions, never on the section. -/
namespace QuaternionicSymmetry.HolomorphicSectionSamplingBounds
open HolomorphicSectionSamplingCharts HolomorphicLineCoreClasses
open HolomorphicLineCorePullback HolomorphicLineCoreProjectiveEvaluation HolomorphicLinePowers
open scoped Manifold ContDiff Topology BigOperators
open Metric Set
noncomputable section

variable {B F : Type} [TopologicalSpace B] [T2Space B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L : LineCore.{0} (B := B) 𝓘(ℂ,F))

theorem coefficient_transition (i j : L.Index) (x : B)
    (hi : x ∈ L.core.baseSet i) (hj : x ∈ L.core.baseSet j)
    (s : GlobalSections 𝓘(ℂ,F) L) :
    chartEvaluation 𝓘(ℂ,F) L i x s = transitionScalar L.core j i x *
      chartEvaluation 𝓘(ℂ,F) L j x s := by
  unfold transitionScalar
  rw [← linear_apply_one]
  exact (L.core.coordChange_comp (L.core.indexAt x) j i x
    ⟨⟨L.core.mem_baseSet_at x,hj⟩,hi⟩ (s x)).symm

theorem exists_transition_bound (c d : SamplingChart L) :
    ∃ C : ℝ, ∀ x ∈ c.outer ∩ d.inner,
      ‖transitionScalar L.core d.index c.index x‖ ≤ C := by
  have hK : IsCompact (c.outer ∩ d.inner) := c.compact_outer.inter_right d.compact_inner.isClosed
  have hc : ContinuousOn (transitionScalar L.core d.index c.index)
      (L.core.baseSet d.index ∩ L.core.baseSet c.index) :=
    (L.core.continuousOn_coordChange d.index c.index).clm_apply continuousOn_const
  exact hK.exists_bound_of_continuousOn (hc.mono (fun x hx =>
    ⟨d.outer_in_base (d.inner_sub_outer hx.2),c.outer_in_base hx.1⟩))

theorem uniform_outer_bound {I : Type} [Fintype I] [Nonempty I]
    (c : I → SamplingChart L) (hcover : ∀ x : B, ∃ i, x ∈ (c i).inner) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : GlobalSections 𝓘(ℂ,F) L) (M : ℝ), 0 ≤ M →
      (∀ i z, z ∈ closedBall (c i).center (c i).radius → ‖(c i).evaluation z s‖ ≤ M) →
      ∀ i z, z ∈ ball (c i).center (3 * (c i).radius) → ‖(c i).evaluation z s‖ ≤ C * M := by
  classical
  choose b hb using fun p : I × I => exists_transition_bound L (c p.1) (c p.2)
  let C := ∑ p : I × I, max 1 (b p)
  have hterm (p : I × I) : max 1 (b p) ≤ C :=
    Finset.single_le_sum (fun q _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ p)
  have hC : 1 ≤ C := (le_max_left _ (b (Classical.arbitrary (I × I)))).trans (hterm _)
  refine ⟨C,hC,?_⟩
  intro s M hM hinner i z hz
  let x := (chartAt F (c i).point).symm z
  have hxi : x ∈ (c i).outer := ⟨z,Metric.ball_subset_closedBall hz,rfl⟩
  obtain ⟨j,hxj⟩ := hcover x
  obtain ⟨w,hw,hwx⟩ := hxj
  have hcoeff : ‖chartEvaluation 𝓘(ℂ,F) L (c j).index x s‖ ≤ M := by
    rw [← hwx]
    exact hinner j w hw
  have hscalar : ‖transitionScalar L.core (c j).index (c i).index x‖ ≤ C :=
    (hb (i,j) x ⟨hxi,⟨w,hw,hwx⟩⟩).trans ((le_max_right _ _).trans (hterm (i,j)))
  change ‖chartEvaluation 𝓘(ℂ,F) L (c i).index x s‖ ≤ C * M
  rw [coefficient_transition L _ _ x ((c i).outer_in_base hxi)
    ((c j).outer_in_base ((c j).inner_sub_outer ⟨w,hw,hwx⟩)),norm_mul]
  exact mul_le_mul hscalar hcoeff (norm_nonneg _) (le_trans zero_le_one hC)

theorem section_eq_zero_of_inner_evaluations {I : Type}
    (c : I → SamplingChart L) (hcover : ∀ x : B, ∃ i, x ∈ (c i).inner)
    (s : GlobalSections 𝓘(ℂ,F) L)
    (hs : ∀ i z, z ∈ closedBall (c i).center (c i).radius → (c i).evaluation z s = 0) :
    s = 0 := by
  ext x
  obtain ⟨i,z,hz,hzx⟩ := hcover x
  have hi : x ∈ L.core.baseSet (c i).index :=
    (c i).outer_in_base ((c i).inner_sub_outer ⟨z,hz,hzx⟩)
  have he : chartEvaluation 𝓘(ℂ,F) L (c i).index x s = 0 := by
    rw [← hzx]
    exact hs i z hz
  have hback := congrArg (L.core.coordChange (c i).index (L.core.indexAt x) x) he
  rw [map_zero] at hback
  change L.core.coordChange (c i).index (L.core.indexAt x) x
    (L.core.coordChange (L.core.indexAt x) (c i).index x (s x)) = 0 at hback
  rw [L.core.coordChange_comp _ _ _ x
    ⟨⟨L.core.mem_baseSet_at x,hi⟩,L.core.mem_baseSet_at x⟩,
    L.core.coordChange_self _ x (L.core.mem_baseSet_at x)] at hback
  exact hback

end
end QuaternionicSymmetry.HolomorphicSectionSamplingBounds
