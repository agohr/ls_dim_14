import QuaternionicSymmetry.HolomorphicPicardIteration

/-! Uniform convergence of the state and its variational Picard iterates
proves complex differentiability of the actual local ODE solution in its
initial point. -/
namespace QuaternionicSymmetry.HolomorphicPicardLimit
open Set Filter Metric ODE Function MeasureTheory HolomorphicPicardIteration
open scoped Topology ContDiff NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local notation "P" => E × (E →L[ℂ] E)
variable {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof (fun _ => variational f) t₀ (x₀,ContinuousLinearMap.id ℂ E) a r L K)

def solutionCurve (x : E) : FunSpace t₀ (x₀,ContinuousLinearMap.id ℂ E) r L := by
  classical
  exact if hx : x ∈ closedBall x₀ r then
    Classical.choose (FunSpace.exists_isFixedPt_next hf (initial_mem hx)) else default

theorem solution_fixed (x : E) (hx : x ∈ closedBall x₀ r) :
    IsFixedPt (FunSpace.next hf (initial_mem hx)) (solutionCurve hf x) := by
  simp only [solutionCurve,dif_pos hx]
  exact Classical.choose_spec (FunSpace.exists_isFixedPt_next hf (initial_mem hx))

def solution (x : E) (t : ℝ) : P := (solutionCurve hf x).compProj t

include hf

theorem curve_distance_le (α β : FunSpace t₀ (x₀,ContinuousLinearMap.id ℂ E) r L) :
    dist α β ≤ 2 * (a : ℝ) := by
  change dist α.toContinuousMap β.toContinuousMap ≤ _
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  have hα : dist (α t) (x₀,ContinuousLinearMap.id ℂ E) ≤ a :=
    FunSpace.mem_closedBall hf.mul_max_le
  have hβ : dist (β t) (x₀,ContinuousLinearMap.id ℂ E) ≤ a :=
    FunSpace.mem_closedBall hf.mul_max_le
  have h := dist_triangle (α t) (x₀,ContinuousLinearMap.id ℂ E) (β t)
  rw [dist_comm (x₀,ContinuousLinearMap.id ℂ E)] at h
  exact h.trans (by linarith)

theorem iterate_distance_le (n : ℕ) (x : E) (hx : x ∈ closedBall x₀ r)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    dist (HolomorphicPicardIteration.iterate f t₀ n x t) (solution hf x t) ≤
      ((K : ℝ) * max (tmax - t₀) (t₀ - tmin)) ^ n / n.factorial * (2 * (a : ℝ)) := by
  have h := FunSpace.dist_iterate_next_iterate_next_le hf (initial_mem hx)
    (constantCurve x hx) (solutionCurve hf x) n
  have hfix := (solution_fixed hf x hx).iterate n
  rw [hfix] at h
  rw [HolomorphicPicardIteration.iterate_eq hf n x hx ⟨t,ht⟩]
  change dist _ ((solutionCurve hf x).compProj t) ≤ _
  rw [FunSpace.compProj_of_mem ht]
  apply (ContinuousMap.dist_apply_le_dist (f :=
    ((FunSpace.next hf (initial_mem hx))^[n] (constantCurve x hx)).toContinuousMap)
    (g := (solutionCurve hf x).toContinuousMap) ⟨t,ht⟩).trans
  apply h.trans
  apply mul_le_mul_of_nonneg_left (curve_distance_le hf _ _)
  have hm : 0 ≤ max (tmax - (t₀ : ℝ)) ((t₀ : ℝ)-tmin) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
  positivity

theorem iterate_tendstoUniformlyOn (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    TendstoUniformlyOn (fun n x => HolomorphicPicardIteration.iterate f t₀ n x t)
      (fun x => solution hf x t) atTop (ball x₀ r) := by
  have hzero := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((K : ℝ) * max (tmax - t₀) (t₀ - tmin))).mul_const (2 * (a : ℝ))
  simp only [zero_mul] at hzero
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  rw [dist_comm]
  exact (iterate_distance_le hf n x (ball_subset_closedBall hx) t ht).trans_lt hn

/-- Complex differentiability of the genuine ODE solution, with the
variational equation giving its derivative. -/
theorem solution_hasFDerivAt
    (hd : ∀ q ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) a, DifferentiableAt ℂ f q.1)
    (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasFDerivAt (fun y => (solution hf y t).1) (solution hf x t).2 x := by
  have hlim := iterate_tendstoUniformlyOn hf t ht
  apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball
    (uniformContinuous_snd.comp_tendstoUniformlyOn hlim)
    (fun n y hy => iterate_hasFDerivAt hf hd n y hy t ht)
    (fun y hy => continuous_fst.continuousAt.tendsto.comp (hlim.tendsto_at hy)) hx

theorem solution_holomorphic
    (hd : ∀ q ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) a, DifferentiableAt ℂ f q.1)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    DifferentiableOn ℂ (fun x => (solution hf x t).1) (ball x₀ r) :=
  fun x hx => (solution_hasFDerivAt hf hd x hx t ht).differentiableAt.differentiableWithinAt

end
end QuaternionicSymmetry.HolomorphicPicardLimit
