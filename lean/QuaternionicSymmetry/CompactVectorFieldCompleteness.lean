import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Topology.Compactness.Compact

/-! Compact smooth manifolds have complete continuously differentiable vector
fields. A local flow with continuous dependence supplies uniform existence
time on a neighborhood; a finite cover supplies one time for the whole manifold.
This is a prerequisite for replacing infinitesimal-automorphism source inputs. -/
namespace QuaternionicSymmetry.CompactVectorFieldCompleteness
open Set Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem local_euclidean_flow {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContinuousOn α (Metric.ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ Metric.ball x₀ r, α (x,0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun t => α (x,t)) (f (α (x,t))) t ∧ α (x,t) ∈ U := by
  obtain ⟨ε,hε,a,r,L,K,hr,hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf 0
  obtain ⟨α,hα,hcont⟩ := hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hdom : Metric.closedBall x₀ (r : ℝ) ×ˢ Icc (-ε) ε ∈ 𝓝 (x₀, (0 : ℝ)) := by
    rw [nhds_prod_eq, Filter.prod_mem_prod_iff]
    exact ⟨Metric.closedBall_mem_nhds x₀ (by exact_mod_cast hr), Icc_mem_nhds (by linarith) hε⟩
  have hcont' : ContinuousAt α (x₀, (0 : ℝ)) := by
    apply hcont.continuousAt
    simpa using hdom
  have heq : α (x₀, (0 : ℝ)) = x₀ := (hα x₀ (Metric.mem_closedBall_self r.coe_nonneg)).1
  have hval : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), α p ∈ U := by
    apply hcont'.eventually
    rw [heq]
    exact hU.mem_nhds hx
  have hfirst : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), p.1 ∈ Metric.closedBall x₀ (r : ℝ) :=
    continuous_fst.continuousAt.eventually (Metric.closedBall_mem_nhds x₀ (by exact_mod_cast hr))
  have hsecond : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), p.2 ∈ Ioo (-ε) ε :=
    continuous_snd.continuousAt.eventually (Ioo_mem_nhds (by linarith) hε)
  obtain ⟨δ,hδ,hgood⟩ := Metric.mem_nhds_iff.mp (hfirst.and (hsecond.and hval))
  have hmem (x : E) (hxδ : x ∈ Metric.ball x₀ (δ / 2)) (t : ℝ) (ht : t ∈ Ioo (-(δ / 2)) (δ / 2)) : (x,t) ∈ Metric.ball (x₀,0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨lt_trans hxδ (by linarith), ?_⟩
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨δ / 2, by positivity, δ / 2, by positivity, α, ?_, ?_⟩
  · apply hcont.mono
    intro p hp
    have hg := hgood (hmem p.1 hp.1 p.2 hp.2)
    exact ⟨hg.1, by simpa using Ioo_subset_Icc_self hg.2.1⟩
  intro x hxδ
  have hzero := hgood (hmem x hxδ 0 (by constructor <;> linarith))
  refine ⟨(hα x hzero.1).1, ?_⟩
  intro t ht
  have hg := hgood (hmem x hxδ t ht)
  refine ⟨?_, hg.2.2⟩
  have hd := (hα x hg.1).2 t (by simpa using Ioo_subset_Icc_self hg.2.1)
  exact hd.hasDerivAt (by simpa using Icc_mem_nhds hg.2.1.1 hg.2.1.2)

theorem local_uniform_euclidean {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ Metric.ball x₀ r,
      ∃ α : ℝ → E, α 0 = x ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (f (α t)) t ∧ α t ∈ U := by
  obtain ⟨r,hr,ε,hε,α,_,hα⟩ := local_euclidean_flow hf hU hx
  exact ⟨r,hr,ε,hε,fun x hx => ⟨fun t => α (x,t),hα x hx⟩⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

set_option maxHeartbeats 800000 in
theorem local_manifold_flow
    (v : (x : M) → TangentSpace 𝓘(ℝ,E) x) (x₀ : M)
    (hv : ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) x₀) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε > (0 : ℝ),
      ∃ β : M × ℝ → M, ContinuousOn β (U ×ˢ Ioo (-ε) ε) ∧
        ∀ x ∈ U, β (x,0) = x ∧ IsMIntegralCurveOn (fun t => β (x,t)) v (Ioo (-ε) ε) := by
  let I := 𝓘(ℝ,E)
  let e := extChartAt I x₀
  rw [contMDiffAt_iff] at hv
  have hx₀ : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hf := (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint hx₀)).snd
  obtain ⟨r,hr,ε,hε,α,hαcont,hflow⟩ := local_euclidean_flow hf isOpen_interior
    ((I.isInteriorPoint_iff).mp hx₀)
  let U := e.source ∩ e ⁻¹' Metric.ball (e x₀) r
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hs := (isOpen_extChartAt_source (I := I) x₀).mem_nhds hx.1
    have hc : ContinuousAt e x := (continuousOn_extChartAt x₀ x hx.1).continuousAt hs
    exact inter_mem hs (hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2))
  let β : M × ℝ → M := fun p => e.symm (α (e p.1,p.2))
  refine ⟨U,hU,⟨mem_extChartAt_source x₀, Metric.mem_ball_self hr⟩,ε,hε,β,?_,?_⟩
  · have hg : ContinuousOn (fun p : M × ℝ => (e p.1,p.2)) (U ×ˢ Ioo (-ε) ε) :=
      ((continuousOn_extChartAt x₀).comp continuousOn_fst (fun p hp => hp.1.1)).prodMk
        continuousOn_snd
    apply (continuousOn_extChartAt_symm (I := I) x₀).comp
      (hαcont.comp hg (fun p hp => ⟨hp.1.2,hp.2⟩))
    intro p hp
    exact interior_subset ((hflow (e p.1) hp.1.2).2 p.2 hp.2).2
  intro x hx
  let f : ℝ → E := fun t => α (e x,t)
  have hα₀ : f 0 = e x := (hflow (e x) hx.2).1
  have hα := (hflow (e x) hx.2).2
  refine ⟨?_,?_⟩
  · change e.symm (f 0) = x
    rw [hα₀]
    exact e.left_inv hx.1
  intro t ht
  let xₜ : M := e.symm (f t)
  have h : HasDerivAt f (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) t := (hα t ht).1
  have hf3 : f t ∈ interior e.target := (hα t ht).2
  have hf3' : f t ∈ e.target := interior_subset hf3
  have hft1 : xₜ ∈ e.source := e.map_target hf3'
  have hft2 := mem_extChartAt_source (I := I) xₜ
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2,hft1⟩,hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
    (mem_nhds_iff.mpr ⟨interior e.target,
      subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hf3⟩)
  rw [← e.right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1,hft2⟩


theorem local_uniform_manifold
    (v : (x : M) → TangentSpace 𝓘(ℝ,E) x) (x₀ : M)
    (hv : ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) x₀) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε > (0 : ℝ),
      ∀ x ∈ U, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  obtain ⟨U,hU,hx,ε,hε,β,_,hβ⟩ := local_manifold_flow v x₀ hv
  exact ⟨U,hU,hx,ε,hε,fun x hx => ⟨fun t => β (x,t),hβ x hx⟩⟩

/-- Compactness makes the locally uniform existence time global. -/
theorem exists_global [CompactSpace M] [T2Space M]
    (v : (x : M) → TangentSpace 𝓘(ℝ,E) x)
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  classical
  choose U hU hmem ε hε hflow using fun y : M => local_uniform_manifold v y (hv y)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun y _ => mem_iUnion.mpr ⟨y,hmem y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨y,hy⟩
  let δ := s.inf' hsne ε
  have hδ : (0 : ℝ) < δ := (Finset.lt_inf'_iff hsne).mpr (fun y _ => hε y)
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hδ _ x
  intro y
  obtain ⟨z,hz,hy⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  obtain ⟨γ,hγ₀,hγ⟩ := hflow z y hy
  refine ⟨γ,hγ₀,hγ.mono ?_⟩
  have hδε : δ ≤ ε z := Finset.inf'_le ε hz
  exact Ioo_subset_Ioo (neg_le_neg hδε) hδε

end
end QuaternionicSymmetry.CompactVectorFieldCompleteness
