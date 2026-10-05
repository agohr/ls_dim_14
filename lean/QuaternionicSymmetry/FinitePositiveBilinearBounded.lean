import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! A positive-definite continuous bilinear form on a finite-dimensional
real normed space has a bounded unit ball in the existing norm topology. -/

namespace QuaternionicSymmetry.FinitePositiveBilinearBounded

open Set Metric Bornology
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Positivity alone gives the unit-ball boundedness needed by the actual
Riemannian metric constructor; no choice of an equivalent norm is assumed. -/
theorem unitBall_isVonNBounded (g : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) :
    IsVonNBounded ℝ {v : V | g v v < 1} := by
  classical
  cases subsingleton_or_nontrivial V
  · rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
    refine ⟨0, fun v _ => ?_⟩
    simp [Subsingleton.elim v (0 : V)]
  · have hc : Continuous (fun v : V => g v v) :=
      g.continuous.clm_apply continuous_id
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
    have hunorm : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
    have hu0 : u ≠ 0 := by
      intro h
      simp [h] at hunorm
    have hm : 0 < g u u := hpos u hu0
    rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
    refine ⟨1 + 1 / (g u u), ?_⟩
    intro v hv
    change g v v < 1 at hv
    by_cases hv0 : v = 0
    · simp only [hv0, norm_zero]
      positivity
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have hn0 : ‖v‖ ≠ 0 := ne_of_gt hn
      have hunit : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
        simp [norm_smul, hn0]
      have hminv : g u u ≤ g (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hmin hunit
      have hscale : g (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) =
          (‖v‖⁻¹)^2 * g v v := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      rw [hscale] at hminv
      have hmul := mul_le_mul_of_nonneg_left hminv (sq_nonneg ‖v‖)
      have hcancel : ‖v‖ ^ 2 * ((‖v‖⁻¹)^2 * g v v) = g v v := by
        field_simp
      rw [hcancel] at hmul
      have hsq : ‖v‖ ^ 2 < 1 / (g u u) := by
        apply (lt_div_iff₀ hm).mpr
        exact hmul.trans_lt hv
      by_contra hlarge
      have hlarge' : 1 + 1 / (g u u) < ‖v‖ := lt_of_not_ge hlarge
      have hinv : 0 < 1 / (g u u) := one_div_pos.mpr hm
      nlinarith [sq_nonneg (‖v‖ - 1)]

end
end QuaternionicSymmetry.FinitePositiveBilinearBounded
