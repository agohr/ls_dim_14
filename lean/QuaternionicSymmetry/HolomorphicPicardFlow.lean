import QuaternionicSymmetry.HolomorphicPicardLimit
import QuaternionicSymmetry.PicardLindelofNeighborhood
import QuaternionicSymmetry.ComplexC1Smooth
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! A local real-time flow with holomorphic dependence on the initial point. -/
namespace QuaternionicSymmetry.HolomorphicPicardFlow
open Set Filter Metric ODE Function MeasureTheory HolomorphicPicardIteration HolomorphicPicardLimit
open scoped Topology ContDiff NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local notation "P" => E × (E →L[ℂ] E)
variable {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof (fun _ => variational f) t₀ (x₀,ContinuousLinearMap.id ℂ E) a r L K)

theorem solution_initial (x : E) (hx : x ∈ closedBall x₀ r) :
    solution hf x t₀ = (x,ContinuousLinearMap.id ℂ E) := by
  change (solutionCurve hf x).compProj t₀ = _
  rw [FunSpace.compProj_val,← solution_fixed hf x hx,FunSpace.next_apply₀]

theorem solution_derivative (x : E) (hx : x ∈ closedBall x₀ r)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (solution hf x) (variational f (solution hf x t)) (Icc tmin tmax) t := by
  let α := solutionCurve hf x
  have hα : IsFixedPt (FunSpace.next hf (initial_mem hx)) α := solution_fixed hf x hx
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn
    (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
    (x,ContinuousLinearMap.id ℂ E) ht |>.congr_of_mem _ ht
  intro t' ht'
  change α.compProj t' = _
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht',FunSpace.next_apply]

theorem solution_continuousOn :
    ContinuousOn (fun p : E × ℝ => solution hf p.1 p.2) (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨B,hB⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ B
    (fun x _ => (solutionCurve hf x).continuous_compProj.continuousOn)
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist ((solutionCurve hf x).compProj t) ((solutionCurve hf y).compProj t) ≤ _
  rw [FunSpace.compProj_of_mem ht,FunSpace.compProj_of_mem ht]
  apply (ContinuousMap.dist_apply_le_dist (f := (solutionCurve hf x).toContinuousMap)
    (g := (solutionCurve hf y).toContinuousMap) ⟨t,ht⟩).trans
  simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using
    hB (x,ContinuousLinearMap.id ℂ E) (y,ContinuousLinearMap.id ℂ E) (initial_mem hx) (initial_mem hy)
      (solutionCurve hf x) (solutionCurve hf y) (solution_fixed hf x hx) (solution_fixed hf y hy)

/-- The actual time maps are continuously complex differentiable. -/
theorem solution_contDiffOn_one
    (hd : ∀ q ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) a, DifferentiableAt ℂ f q.1)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    ContDiffOn ℂ 1 (fun x => (solution hf x t).1) (ball x₀ r) := by
  have hder : Set.EqOn (fderiv ℂ (fun x => (solution hf x t).1))
      (fun x => (solution hf x t).2) (ball x₀ r) :=
    fun x hx => (solution_hasFDerivAt hf hd x hx t ht).fderiv
  have hc : ContinuousOn (fun x => (solution hf x t).2) (ball x₀ r) :=
    (solution_continuousOn hf).snd.comp (continuousOn_id.prodMk continuousOn_const)
      (fun x hx => ⟨ball_subset_closedBall hx,ht⟩)
  have hh : ContDiffOn ℂ (0 + 1) (fun x => (solution hf x t).1) (ball x₀ r) :=
    (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).2
      ⟨solution_holomorphic hf hd t ht,by simp,contDiffOn_zero.mpr (hc.congr hder)⟩
  simpa using hh

/-- Holomorphic vector fields admit actual local flows whose time maps are
holomorphic. The whole flow is also jointly continuous. -/
theorem local_flow {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℂ ∞ f U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContDiffOn ℂ 1 (fun x => α (x,t)) (ball x₀ r)) ∧
      ∀ x ∈ ball x₀ r, α (x,0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun t => α (x,t)) (f (α (x,t))) t ∧ α (x,t) ∈ U := by
  let q₀ : P := (x₀,ContinuousLinearMap.id ℂ E)
  let W : Set P := Prod.fst ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_fst
  have hq₀ : q₀ ∈ W := hx₀
  have hG : ContDiffOn ℂ ∞ (variational f) W := by
    apply (hf.comp contDiffOn_fst (fun q hq => hq)).prodMk
    exact ((hf.fderiv_of_isOpen hU (by simp)).comp contDiffOn_fst
      (fun q hq => hq)).clm_comp contDiffOn_snd
  have hGreal : ContDiffAt ℝ 1 (variational f) q₀ :=
    ((hG.contDiffAt (hW.mem_nhds hq₀)).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).restrict_scalars ℝ
  obtain ⟨ε,hε,a,r,L,K,hr,hball,hpl⟩ := PicardLindelofNeighborhood.within_neighborhood
    hGreal (hW.mem_nhds hq₀) 0
  have hpl' : IsPicardLindelof (fun _ => variational f)
      (tmin := -ε) (tmax := ε) ⟨0,by constructor <;> linarith⟩ q₀ a r L K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      exact hpl.lipschitzOnWith t (by simpa using ht)
    · intro q hq
      exact (hpl.continuousOn q hq).mono (by intro t ht; simpa using ht)
    · intro t ht q hq
      exact hpl.norm_le t (by simpa using ht) q hq
    · simpa using hpl.mul_max_le
  let α : E × ℝ → E := fun p => (solution hpl' p.1 p.2).1
  refine ⟨r,by exact_mod_cast hr,ε,hε,α,?_,?_,?_⟩
  · exact (solution_continuousOn hpl').fst.mono
      (Set.prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  · intro t ht
    apply (solution_contDiffOn_one hpl' (fun q hq =>
      (hf.differentiableOn (by simp) q.1 (hball hq)).differentiableAt
        (hU.mem_nhds (hball hq))) t (Ioo_subset_Icc_self ht))
  · intro x hx
    refine ⟨congrArg Prod.fst (solution_initial hpl' x (ball_subset_closedBall hx)),?_⟩
    intro t ht
    refine ⟨?_,?_⟩
    · exact ((solution_derivative hpl' x (ball_subset_closedBall hx) t
        (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).fst
    · exact hball ((solutionCurve hpl' x).compProj_mem_closedBall hpl'.mul_max_le)

/-- Smooth holomorphic local flows in finite-dimensional complex domains. -/
theorem local_flow_smooth [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℂ ∞ f U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContDiffOn ℂ ∞ (fun x => α (x,t)) (ball x₀ r)) ∧
      ∀ x ∈ ball x₀ r, α (x,0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun t => α (x,t)) (f (α (x,t))) t ∧ α (x,t) ∈ U := by
  obtain ⟨r,hr,ε,hε,α,hcont,hC1,hα⟩ := local_flow hU hx₀ hf
  exact ⟨r,hr,ε,hε,α,hcont,fun t ht => ComplexC1Smooth.contDiffOn_infty_of_one isOpen_ball (hC1 t ht),hα⟩

end
end QuaternionicSymmetry.HolomorphicPicardFlow
