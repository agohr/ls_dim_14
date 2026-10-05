import Mathlib.Analysis.ODE.PicardLindelof

/-! Local ODE bounds can be chosen inside any prescribed neighborhood. -/
namespace QuaternionicSymmetry.PicardLindelofNeighborhood
open Set Filter Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem within_neighborhood {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    {U : Set E} (hU : U ∈ 𝓝 x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r),
      closedBall x₀ a ⊆ U ∧ IsPicardLindelof (fun _ => f)
        (tmin := t₀-ε) (tmax := t₀+ε) ⟨t₀,by simp [le_of_lt hε]⟩ x₀ a r L K := by
  obtain ⟨K,s,hs,hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a,ha,has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hU)
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x ∈ closedBall x₀ (a/2)) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x-x₀‖ + ‖f x₀‖ := by
        gcongr
        rw [← dist_eq_norm,← dist_eq_norm]
        exact hl.dist_le_mul x (has (closedBall_subset_ball (half_lt_self ha) hx)).1
          x₀ (mem_of_mem_nhds hs)
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ ≤ _ := le_add_of_nonneg_right zero_le_one
  let ε := a/L/2/2
  have hε : 0 < ε := by positivity
  refine ⟨ε,hε,⟨a/2,(half_pos ha).le⟩,⟨a/2,(half_pos ha).le⟩/2,
    ⟨L,hL0.le⟩,K,half_pos (half_pos ha),?_,?_⟩
  · intro x hx
    exact (has (closedBall_subset_ball (half_lt_self ha) hx)).2
  apply IsPicardLindelof.of_time_independent hb
    (hl.mono (fun x hx => (has (closedBall_subset_ball (half_lt_self ha) hx)).1))
  rw [NNReal.coe_mk,add_sub_cancel_left,sub_sub_cancel,max_self,NNReal.coe_div,
    NNReal.coe_two,NNReal.coe_mk,mul_comm,← le_div_iff₀ hL0,sub_half,div_right_comm (a/2),
    div_right_comm a]

end QuaternionicSymmetry.PicardLindelofNeighborhood
