import QuaternionicSymmetry.QuaternionicAction
import QuaternionicSymmetry.QuaternionicFrame
import Mathlib.Tactic

open scoped Quaternion
open Quaternion

namespace QuaternionicSymmetry.QuaternionicStructure

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def actionCoeffs (q : ℍ) : Fin 4 → ℝ := ![q.re, q.imI, q.imJ, q.imK]

private theorem action_eq_frame_sum (Q : QuaternionicStructure V) (q : ℍ) (v : V) :
    Q.action q v = ∑ i, actionCoeffs q i • Q.frame v i := by
  rw [Fin.sum_univ_four]
  simp [action_apply, actionCoeffs, frame]

/-- The quaternion action scales the real norm by the quaternion norm. -/
theorem norm_action (Q : QuaternionicStructure V) (q : ℍ) (v : V) :
    ‖Q.action q v‖ = ‖q‖ * ‖v‖ := by
  have hinner : inner ℝ (Q.action q v) (Q.action q v) =
      Quaternion.normSq q * inner ℝ v v := by
    rw [action_eq_frame_sum]
    rw [sum_inner]
    simp_rw [inner_sum]
    simp only [real_inner_smul_left, real_inner_smul_right]
    simp_rw [Q.frame_gram]
    simp [actionCoeffs, Fin.sum_univ_four]
    rw [Quaternion.normSq_def']
    ring
  have hnorm : ‖Q.action q v‖ ^ 2 = Quaternion.normSq q * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (Q.action q v),
      ← real_inner_self_eq_norm_sq v]
    exact hinner
  rw [Quaternion.normSq_eq_norm_mul_self] at hnorm
  have hprod : (‖q‖ * ‖v‖) ^ 2 = ‖q‖ ^ 2 * ‖v‖ ^ 2 := by ring
  have hp : 0 ≤ ‖q‖ * ‖v‖ := mul_nonneg (norm_nonneg q) (norm_nonneg v)
  have hsq : ‖Q.action q v‖ ^ 2 = (‖q‖ * ‖v‖) ^ 2 := by
    nlinarith [hnorm, hprod]
  nlinarith [hsq, norm_nonneg (Q.action q v), sq_nonneg (‖Q.action q v‖ + ‖q‖ * ‖v‖)]

end
end QuaternionicSymmetry.QuaternionicStructure

namespace QuaternionicSymmetry.QuaternionicStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem action_unit_bijective (Q : QuaternionicStructure V) (q : ℍ)
    (hq : ‖q‖ = 1) : Function.Bijective (Q.action q) := by
  have hq0 : q ≠ 0 := by
    intro hzero
    simp [hzero] at hq
  have hinv : Function.LeftInverse (Q.action q⁻¹) (Q.action q) := by
    intro v
    change (Q.action q⁻¹ * Q.action q) v = v
    calc
      (Q.action q⁻¹ * Q.action q) v = Q.action (q⁻¹ * q) v := by
        exact congrArg (fun T : Module.End ℝ V => T v) (Q.action.map_mul q⁻¹ q).symm
      _ = v := by simp [hq0]
  have hinv' : Function.RightInverse (Q.action q⁻¹) (Q.action q) := by
    intro v
    change (Q.action q * Q.action q⁻¹) v = v
    calc
      (Q.action q * Q.action q⁻¹) v = Q.action (q * q⁻¹) v := by
        exact congrArg (fun T : Module.End ℝ V => T v) (Q.action.map_mul q q⁻¹).symm
      _ = v := by simp [hq0]
  exact ⟨hinv.injective, hinv'.surjective⟩

/-- The action of a unit quaternion is an actual real-linear isometry. -/
noncomputable def unitAction (Q : QuaternionicStructure V) (q : ℍ)
    (hq : ‖q‖ = 1) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (Q.action q) (action_unit_bijective Q q hq))
    (fun v => by
      change ‖Q.action q v‖ = ‖v‖
      rw [Q.norm_action, hq, one_mul])

@[simp] theorem unitAction_apply (Q : QuaternionicStructure V) (q : ℍ)
    (hq : ‖q‖ = 1) (v : V) : Q.unitAction q hq v = Q.action q v := rfl

end QuaternionicSymmetry.QuaternionicStructure
